# MIT License
#
# Copyright (c) 2017 Alex Ignatov
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

# -*- coding: utf-8 -*-
import ctypes
import json
import multiprocessing
import os
import os.path
import re
import shutil
import tempfile
import time
import random
from  collections import OrderedDict
from ctypes import *
from ctypes.wintypes import RECT, DWORD, LONG, WORD, LPVOID, LPCWSTR, HWND, POINT, UINT, INT
from  multiprocessing import Process
from operator import itemgetter

import cv2
import itertools
import numpy as np

DEBUG = False
STATS_DIR = 'stats'
PATTERNS_DIR='patterns'
FARMING_INTERVAL = 30
PROGRESSION_INTERVAL = 30
FISHING_INTERVAL = 30
ASCENSION_INTERVAL = 10800
TOP_HEROES_UPGRADE_INTERVAL = 120
ALL_HEROES_UPGRADE_INTERVAL = 10
ALL_HEROES_UPGRADE_MAX_TIMER = 3600
MAX_NUMBER_OF_VISIBLE_HEROES = 5

WM_MOUSEWHEEL = 0x020A
WHEEL_DOWN = -1
WHEEL_UP = 1

WHEEL_DELTA = 120
WM_LBUTTONDOWN = 0x0201
WM_LBUTTONUP = 0x0202
WM_MOUSEMOVE = 0x0200
WM_MOUSELEAVE = 0x02A3
WM_MOUSEHOVER = 0x02A1
HTCLIENT = 1
WM_SETCURSOR = 0x0020
WM_CHAR = 0x0102
WM_KEYDOWN = 0x0100
WM_KEYUP = 0x0101
HWND_TOP = 0x0
SWP_NOMOVE = 0x0002
VK_CONTROL = 0x11
VK_SHIFT = 0x10
BI_RGB = 0x0000
DIB_RGB_COLORS = 0x00
SRCCOPY = 0xCC0020
SW_SHOWMINIMIZED = 0x2
SW_SHOWNORMAL = 0x1
SW_SHOWMAXIMIZED = 0x3
SW_RESTORE = 0x9
SW_MINIMIZE = 6
SW_SHOWMINNOACTIVE = 7
SW_SHOWNOACTIVATE = 4
SW_HIDE = 0x0

GWL_EXSTYLE = -20
GWL_STYLE = -16
WS_EX_LAYERED = 0x00080000
LWA_ALPHA = 0x00000002
SPI_GETANIMATION = 0x0048
SPI_SETANIMATION = 0x0049
SPIF_SENDCHANGE = 2
WS_MINIMIZEBOX = 0x00020000
WS_MAXIMIZEBOX = 0x00010000
WS_VSCROLL = 0x00200000
WS_HSCROLL = 0x00100000
WS_SIZEBOX = 0x00040000

WS_CAPTION = 0x00C00000
WS_SYSMENU = 0x00080000
SendMessage = ctypes.windll.user32.SendMessageW
FindWindow = ctypes.windll.user32.FindWindowW
FindWindow.argtypes = [LPCWSTR, LPCWSTR]
FindWindow.restype = HWND

SetForegroundWindow = ctypes.windll.user32.SetForegroundWindow
SetWindowPos = ctypes.windll.user32.SetWindowPos
GetWindowRect = ctypes.windll.user32.GetWindowRect
AdjustWindowRect = ctypes.windll.user32.AdjustWindowRect
GetwDesktopWindow = ctypes.windll.user32.GetDesktopWindow
GetWindowRect = ctypes.windll.user32.GetWindowRect
ClientToScreen = ctypes.windll.user32.ClientToScreen
GetClientRect = ctypes.windll.user32.GetClientRect
GetWindowDC = ctypes.windll.user32.GetWindowDC
GetDC = ctypes.windll.user32.GetDC
GetDIBits = ctypes.windll.gdi32.GetDIBits
GetObject = ctypes.windll.gdi32.GetObjectW
CreateBitmap = ctypes.windll.Gdi32.CreateBitmap
CreateCompatibleDC = ctypes.windll.Gdi32.CreateCompatibleDC
CreateCompatibleBitmap = ctypes.windll.Gdi32.CreateCompatibleBitmap
EnumWindows = ctypes.windll.user32.EnumWindows
BitBlt = ctypes.windll.Gdi32.BitBlt
SelectObject = ctypes.windll.Gdi32.SelectObject
GetWindowPlacement = ctypes.windll.user32.GetWindowPlacement
ShowWindow = ctypes.windll.user32.ShowWindow
PrintWindow = ctypes.windll.user32.PrintWindow
GetWindowLong = ctypes.windll.user32.GetWindowLongW
SetWindowLong = ctypes.windll.user32.SetWindowLongW
SetLayeredWindowAttributes = ctypes.windll.user32.SetLayeredWindowAttributes
SystemParametersInfo = ctypes.windll.user32.SystemParametersInfoW
IsIconic = ctypes.windll.user32.IsIconic

ReleaseDC = ctypes.windll.user32.ReleaseDC
DeleteObject = ctypes.windll.gdi32.DeleteObject
DeleteDC = ctypes.windll.Gdi32.DeleteDC


def charToKeyCode(char):
    if char in ('1', '2', '3', '4', '5', '6', '7', '8', '9', '0'):
        return 0x30 + (ord(char) - ord('0'))
    if char == 'ctrl':
        return VK_CONTROL
    if char == 'shift':
        return VK_SHIFT
    if 'a' <= char <= 'z':
        return 0x41 + (ord(char) - ord('a'))
    return None


class BITMAPINFOHEADER(Structure):
    _fields_ = [("biSize", DWORD),
                ("biWidth", LONG),
                ("biHeight", LONG),
                ("biPlanes", WORD),
                ("biBitCount", WORD),
                ("biCompression", DWORD),
                ("biSizeImage", DWORD),
                ("biXPelsPerMeter", LONG),
                ("biYPelsPerMeter", LONG),
                ("biClrUsed", DWORD),
                ("biClrImportant", DWORD)]


class BITMAP(Structure):
    _fields_ = [("bmType", LONG),
                ("bmWidth", LONG),
                ("bmHeight", LONG),
                ("bmWidthBytes", LONG),
                ("bmPlanes", WORD),
                ("bmBitsPixel", WORD),
                ("bmBits", LPVOID)]


class WINDOWPLACEMENT(Structure):
    _fields_ = [("length", UINT),
                ("flags", UINT),
                ("showCmd", UINT),
                ("ptMinPosition", POINT),
                ("ptMaxPosition", POINT),
                ("rcNormalPosition", RECT)]


class ANIMATIONINFO(Structure):
    _fields_ = [("cbSize", UINT),
                ("iMinAnimate", INT)]


def find_single_grey_old(image, pattern, method=cv2.TM_CCOEFF_NORMED, threshold=0.8):
    height_pattern, width_pattern = pattern.getSize()
    height_image, width_image = image.getSize()
    if height_pattern > height_image or width_pattern > width_image:
        if DEBUG:
            print('find_single_grey: Pattern size if greater than image size ')
        return None
    pattern_array = pattern.get_grey_array()
    image_array = image.get_grey_array()
    try:
        res = cv2.matchTemplate(image_array, pattern_array, method)
    except cv2.error as e:
        print('find_single_grey: catch cv2 exception!!! %s ' % str(e))
        # cv2.imshow('image', image)
        # cv2.imshow('pimage', pimage)
        # cv2.waitKey()
        return None
    min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(res)
    if method in [cv2.TM_SQDIFF, cv2.TM_SQDIFF_NORMED] and min_val <= 1 - threshold:
        top_left = min_loc

    elif max_val >= threshold:
        top_left = max_loc
    else:
        # if image.name == '123456':
        #     cv2.imshow('image', image_array)
        #     cv2.imshow('pimage', pattern_array)
        #     cv2.waitKey(50)
        return None
    # cv2.rectangle(image.get_array(), top_left,
    #               (top_left[0] + width, top_left[1] + height),
    #               (0, 0, 255),
    #               1)
    return [Region(top_left[0], top_left[1], width_pattern, height_pattern)]


def find_lvlup(image, pattern,all=False):
    t_min = 128
    t_max = 255
    reg = find_single_grey(image, pattern)
    if not reg:
        return None
    reg = reg[0]
    pat_max = pattern.get_threshold(t_min, t_max).get_array().max()
    tcc = image.crop_copy(reg).get_threshold(t_min, t_max).get_array().max()
    if tcc != pat_max:
        return None
    return [reg]


def find_progress_button(image, pattern):
    return find_single_grey(image, pattern, threshold=0.9,all=all)


def find_single_grey_90(image, pattern,all=False):
    return find_single_grey(image, pattern, threshold=0.9,all=all)


def find_single_grey_95(image, pattern,all=False):
    return find_single_grey(image, pattern, threshold=0.95,all=all)


def find_single_grey_97(image, pattern,all=False):
    return find_single_grey(image, pattern, threshold=0.97,all=all)


def find_level(image, pattern,all=False):
    image = image.get_threshold(235, 255)
    pattern = pattern.get_threshold(235, 255)
    return find_single_grey(image, pattern, threshold=0.96,all=all)


def find_checked_skills(image, pattern,all=False,parts=1):
    image = image.get_threshold(128, 255)
    pattern = pattern.get_threshold(128, 255)
    for sect in np.array_split(pattern,parts,axis=0):

        cv2.imshow("find_checked_skills:image", image.get_array())
        cv2.imshow("find_checked_skills:pattern", pattern.get_array())
        cv2.waitKey(50)
        sect_reg=find_single_grey(image, sect, threshold=0.90)
        if not sect_reg:
            return None


    return find_single_grey(image, pattern, threshold=0.90)

def find_single_grey(image, pattern, method=cv2.TM_CCOEFF_NORMED, threshold=0.8,all=False):
    pattern_height, pattern_width = pattern.getSize()
    height_image, width_image = image.getSize()

    if pattern_height > height_image or pattern_width > width_image:
        if DEBUG:
            print('find_single_grey: Pattern size if greater than image size ')
        return None
    pattern_grey = pattern.get_grey_array()
    image_grey = image.get_grey_array()
    if all:
        image_grey = image_grey.copy()

    regions=[]
    while 1:
        try:
            res = cv2.matchTemplate(image_grey, pattern_grey, method)
        except cv2.error as e:
            print('find_single_grey: catch cv2 exception!!! %s ' % str(e))
            # cv2.imshow('image', image)
            # cv2.imshow('pimage', pimage)
            # cv2.waitKey()
            return None
        min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(res)
        if method in [cv2.TM_SQDIFF, cv2.TM_SQDIFF_NORMED] and min_val <= 1 - threshold:
            top_left = min_loc
        elif max_val >= threshold:
            top_left = max_loc
        else:
            # if image.name == '123456':
            #     cv2.imshow('image', image_array)
            #     cv2.imshow('pimage', pattern_array)
            #     cv2.waitKey(50)
            break
        regions.append(Region(top_left[0], top_left[1], pattern_width, pattern_height))
        if not all:
            break
        cv2.rectangle(image_grey, top_left,
                      (top_left[0] + pattern_width, top_left[1] + pattern_width),
                      (0, 0, 0),
                      cv2.FILLED)
    # return [Region(top_left[0], top_left[1], pattern_width, pattern_height)]
    return regions
def find_all_grey_old(image, pattern, method=cv2.TM_CCOEFF_NORMED, threshold=0.8):
    height, width = pattern.getSize()
    # pimage = pattern.get_canny_array()
    # image = image.get_canny_array()
    pimage = pattern.get_grey_array()
    image = image.get_grey_array()
    res = cv2.matchTemplate(image, pimage, method)
    # res = ((res - res.min()) / (res.max() - res.min()))
    cv2.imshow('find_all_grey', res)
    cv2.waitKey(500)
    min_val, max_val, min_loc, max_loc = cv2.minMaxLoc(res)
    if method in [cv2.TM_SQDIFF, cv2.TM_SQDIFF_NORMED]:
        loc = np.where(res <= 1 - threshold)
    else:
        loc = np.where(res >= threshold)
    regArr = []
    for pt in zip(*loc[::-1]):
        val = res.item(pt[1], pt[0])
        print("find_all_grey: val %s, location %s " % (val, pt))
        reg = Region(pt[0], pt[1], width, height)
        regArr.append((reg, val))
    regRet = []
    valRet = []
    while regArr:
        # Get first region from regArr
        cr = regArr[0][0]

        # Create array of regions which intersect with cr

        intersect_reg = [r for r in regArr if cr.is_intersect(r[0])]
        # Sort it by res value in descending order
        intersect_reg.sort(key=itemgetter(1), reverse=True)
        # Append to returned array region with highest res value
        reg = intersect_reg[0][0]
        val = intersect_reg[0][1]
        regRet.append(reg)
        valRet.append(val)
        # cv2.rectangle(image.img, (reg.x, reg.y),
        #               (reg.getRight(), reg.getBottom()),
        #               (0, 0, 255),
        #               1)
        # Keep region regArr which is not intersected with  crfor pt in zip(*loc[::-1]):
        #     reg = Region(pt[0], pt[1], width, height)
        #     cv2.rectangle(image.img, (reg.x, reg.y),
        #                   (reg.getRight(), reg.getBottom()),
        #                   color,
        #                   thickness)
        regArr = [r for r in regArr if r not in intersect_reg]
    return regRet


def find_pattern_hist(image, pattern, method=cv2.TM_CCOEFF_NORMED, threshold=0.8, corr_coeff=0.9,all=False):
    pattern_grey = pattern.get_grey()
    image_grey = image.get_grey()
    reg_list = find_single_grey(image_grey, pattern_grey, method=method, threshold=threshold,all=all)
    print('find_pattern_hist: reg_list %s' % (reg_list))
    pattern_region = None
    if reg_list:
        img1 = None
        img2 = None
        corr_prev = None
        for reg in reg_list:
            img1 = pattern
            img2 = image.crop(reg)

            # hist_img1 = cv2.calcHist([img1.get_grey_array()], [0], None, [32], [0, 256])
            # hist_img2 = cv2.calcHist([img2.get_grey_array()], [0], None, [32], [0, 256])
            # corr_color = []
            # corr_grey=[]
            # for i in range(1):
            hist_img1 = cv2.calcHist([img1.get_hsv_array()], [0, 1], None, [180, 256], [0, 180, 0, 256])
            #     # hist_img1 = cv2.calcHist([img1.get_array()], [i], None, [256], [0, 256])
            #     # hist_img2 = cv2.calcHist([img2.get_array()], [i], None, [256], [0, 256])
            #     corr_color.append(cv2.compareHist(hist_img1, hist_img2, cv2.HISTCMP_CORREL))
            #
            hist_img2 = cv2.calcHist([img2.get_hsv_array()], [0, 1], None, [180, 256], [0, 180, 0, 256])
            #     # hist_img1 = cv2.calcHist([img1.get_array()], [0], None, [8], [0, 256])
            #     # hist_img2 = cv2.calcHist([img2.get_array()], [0], None, [8], [0, 256])
            #     # hist_img1 = cv2.calcHist([(cv2.medianBlur(img1.get_grey_array(), 3))], [0], None, [256],
            #     #                          [0, 256])
            #     # hist_img2 = cv2.calcHist([(cv2.medianBlur(img2.get_grey_array(), 3))], [0], None, [256],
            #     #                          [0, 256])
            #     # hist_img1 = cv2.calcHist([img1.get_grey_array()], [0], None, [256],
            #     #                          [0, 256])
            #     # hist_img2 = cv2.calcHist([img2.get_grey_array()], [0], None, [256],
            #     #                          [0, 256])
            corr_grey = cv2.compareHist(hist_img1, hist_img2, cv2.HISTCMP_CORREL)

            # print('find_pattern_hist: %s to %s corr_color is B %s G %s R %s corr_grey =%s' % (
            print('find_pattern_hist: %s to %s corr_grey =%s' % (
                # img1.get_name(), img2.get_name(), corr_color[0], corr_color[1], corr_color[2], corr_grey))
                img1.get_name(), img2.get_name(), corr_grey))
            print('find_pattern_hist: img1.getSize() %s to img2.getSize() %s' % (img1.getSize(), img2.getSize()))

            # if pattern.get_name()=='.\\patterns\\main\\fish_1.png':
            #
            #     x_size = 300
            #
            #     for img in (img1, img2):
            #         y_size = int(x_size / img.get_array().shape[1] * img.get_array().shape[0])
            #         cv2.namedWindow(img.get_name(), cv2.WINDOW_NORMAL)
            #         cv2.resizeWindow(img.get_name(), x_size, y_size)
            #         cv2.imshow(img.get_name(),cv2.medianBlur(img.get_array(),3))
            #     cv2.waitKey(500)
            #     pass

            # if min(corr_color) >= corr_coeff or corr_grey >= corr_coeff:
            # if  corr_grey >= corr_coeff:
            if corr_grey >= corr_coeff:
                pattern_region = reg_list
                #     corr_prev = corr_color
                #     # print('find_pattern_hist: %s to %s corr is %s' % (img1.get_name(), img2.get_name(), corr_prev))
                #     # If pattern_region is not already create do it
                #     if not pattern_region:
                #         pattern_region = []
                #
                #     if not pattern_region or not pattern_region[-1].is_intersect(reg):
                #         pattern_region.append(reg)
                #         # cv2.rectangle(self.img, (reg.getLeft(), reg.getTop()),
                #         #               (reg.getRight(), reg.getBottom()),
                #         #               (0, 0, 255),
                #         #               1)
                #         # if corr_prev and corr_prev <= corr:
                #         # reg_ret = reg
        print('find_pattern_hist: %s to %s is %s. pattern_region ' % (img1.get_name(), img2.get_name(), corr_prev))

    return pattern_region


def find_all_grey_multi(image, pattern, method=cv2.TM_CCOEFF_NORMED, threshold=0.8):
    height, width = pattern.getSize()
    # pimage = cv2.medianBlur(pattern.get_canny_array(), 3)
    # image = cv2.medianBlur(image.get_canny_array(),3)
    # pimage = cv2.blur(pattern.get_array(), (3, 3))
    # image = cv2.blur(image.get_array(), (3, 3))
    # pimage=cv2.cvtColor(pimage, cv2.COLOR_BGR2GRAY)
    # image = cv2.cvtColor(image, cv2.COLOR_BGR2GRAY)
    # pimage = cv2.Canny(pimage, 100, 200)
    # image = cv2.Canny(image, 100, 200)
    # pimage = pattern.get_grey_array()
    # image = image.get_grey_array()
    pimage = pattern.get_canny_array()
    image = image.get_canny_array()
    set_list = []
    for method in [cv2.TM_SQDIFF, cv2.TM_CCOEFF]:

        res = cv2.matchTemplate(image, pimage, method)
        # cv2.normalize(res,res,0,1,norm_type=cv2.NORM_MINMAX)
        # Normilized res values in 0..1
        res = ((res - res.min()) / (res.max() - res.min()))
        # if pattern.get_name() == '.\\patterns\\main\\heroes_menu_active.PNG':
        #     cv2.imshow(pattern.get_name(), pattern.get_array())
        #     cv2.imshow(image.get_name(), image.get_array())
        #     cv2.waitKey()


        # cv2.imshow('res', res)
        # cv2.imshow('template', pimage)
        # cv2.waitKey(300)

        if method in [cv2.TM_SQDIFF, cv2.TM_SQDIFF_NORMED]:
            # Find the most minimal value in res
            sort = np.sort(res, axis=None)[0:10]
            sort = np.where(sort < 1 - threshold)
        else:
            # Find the maximum values in res
            sort = np.sort(res, axis=None)[:-10:-1]

        # Find sorted res indext
        ix = np.in1d(res.ravel(), sort).reshape(res.shape)
        loc = np.where(ix)
        regArr = []
        if method == cv2.TM_SQDIFF_NORMED:
            color = (0, 0, 255)
            thickness = 3
        elif method == cv2.TM_CCOEFF_NORMED:
            color = (0, 255, 0)
            thickness = 2
        elif method == cv2.TM_CCORR_NORMED:
            color = (255, 0, 0)
            thickness = 1

        # return regArr
        for pt in zip(*loc[::-1]):
            val = res.item(pt[1], pt[0])
            print("res %s %s " % (val, pt))
            reg = Region(pt[0], pt[1], width, height)
            regArr.append((reg, res.item(pt[1], pt[0])))

        # return regArr

        regRet = []

        while regArr:
            # Get first region from regArr
            cr = regArr[0][0]

            # Create array of regions which intersect with cr

            intersect_reg = [r for r in regArr if cr.is_intersect(r[0])]
            # Sort it by res value in descending order
            intersect_reg.sort(key=itemgetter(1), reverse=True)
            # Append to returned array region with highest res value
            reg = intersect_reg[0][0]
            regRet.append(reg)
            # cv2.rectangle(image.img, (reg.x, reg.y),
            #               (reg.getRight(), reg.getBottom()),
            #               (0, 0, 255),
            #               1)
            # Keep region regArr which is not intersected with  crfor pt in zip(*loc[::-1]):
            #     reg = Region(pt[0], pt[1], width, height)
            #     cv2.rectangle(image.img, (reg.x, reg.y),
            #                   (reg.getRight(), reg.getBottom()),
            #                   color,
            #                   thickness)
            regArr = [r for r in regArr if r not in intersect_reg]
        #

        set_list.append(set(regRet))
    # Find instersection of regions created by different methods
    # Suppose that this
    regRet = set.intersection(*set_list)
    for reg in regRet:
        cv2.rectangle(image.img, (reg.x, reg.y),
                      (reg.getRight(), reg.getBottom()),
                      (255, 255, 255),
                      4)
    if not regRet:
        return None
    return regRet


class Image:
    def __init__(self, name=None, find_in_func=find_single_grey):
        self.img = None
        self.img_buffer = None
        self.name = name
        self.pattern_finder = find_in_func

        # print("Image:__init__: name %s  pattern_finder %s", name, self.pattern_finder)
        pass

    @classmethod
    def fromFile(cls, path, name=None, find_in_func=find_single_grey, method=cv2.IMREAD_COLOR):

        image = Image(name=(name if name is not None else path), find_in_func=find_in_func)
        image.img = cv2.imread(path, method)
        return image

    @classmethod
    def fromArray(cls, arr):
        image = Image('from array %s' % (id(arr)))
        image.img = arr
        return image

    def set_pattern_finder(self, find_in_func):
        self.pattern_finder = find_in_func

    def crop(self, region):
        arr = self.get_array()[region.getTop():region.getBottom(), region.getLeft():region.getRight()]
        img = Image.fromArray(arr)
        img.set_name('cropped at top %s bottom %s left %s rigth %s of %s' % (
            region.getTop(), region.getBottom(), region.getLeft(), region.getRight(), self.get_name()))
        return img

    def crop_copy(self, region):
        arr = self.get_array()[region.getTop():region.getBottom(), region.getLeft():region.getRight()].copy()
        img = Image.fromArray(arr)
        img.set_name('cropped at top %s bottom %s left %s rigth %s of %s' % (
            region.getTop(), region.getBottom(), region.getLeft(), region.getRight(), self.get_name()))

        return img

    def show(self, time=0):
        cv2.imshow(self.get_name(), self.img)
        cv2.waitKey(time)

    def get_array(self):
        return self.img

    def get_threshold(self, low, high, method=cv2.THRESH_BINARY):
        ret, thresh1 = cv2.threshold(self.get_grey_array(), low, high, method)
        return self.fromArray(thresh1)

    def get_grey(self):
        if self.is_grey():
            return self
        return self.fromArray(cv2.cvtColor(self.img, cv2.COLOR_BGR2GRAY))

    def get_grey_array(self):
        if self.is_grey():
            return self.img
        return cv2.cvtColor(self.img, cv2.COLOR_BGR2GRAY)

    def get_canny_array(self):
        return cv2.Canny(self.img, 100, 200)

    def get_hsv_array(self):
        return cv2.cvtColor(self.img, cv2.COLOR_BGR2HSV)

    def get_width(self):
        return self.img.shape[:2][1]

    def get_height(self):
        return self.img.shape[:2][0]

    def getSize(self):
        return self.img.shape[:2]

    def is_grey(self):
        return len(self.img.shape) == 2

    def resize(self, w, h):
        if (self.get_height() == h and self.get_width() == w):
            return

        w_c = float(w) / self.get_width()
        h_c = float(h) / self.get_height()
        if w_c < 1 or h_c < 1:
            method = cv2.INTER_AREA
        else:
            method = cv2.INTER_LINEAR
        self.img = cv2.resize(self.img, None, fx=w_c, fy=h_c, interpolation=method)

    def get_resized_copy(self, w=None, h=None):
        if w is None and h is None:
            raise AttributeError("Image:get_resize_copy: Width and height cant be None both simultaneously")

        if (self.get_height() == h and self.get_width() == w):
            return
        if w:
            w_c = float(w) / self.get_width()
        else:
            w_c = float(h) / self.get_height()

        if h:
            h_c = float(h) / self.get_height()
        else:
            h_c = float(w) / self.get_width()

        if w_c < 1 or h_c < 1:
            method = cv2.INTER_AREA
        else:
            method = cv2.INTER_LINEAR
        return Image.fromArray(cv2.resize(self.img, None, fx=w_c, fy=h_c, interpolation=method))

    def resize(self, scale):
        if scale == 1:
            return
        elif scale < 1:
            method = cv2.INTER_AREA
        elif scale > 1:
            method = cv2.INTER_LINEAR
        self.img = cv2.resize(self.img, None, fx=scale, fy=scale, interpolation=method)

    def get_name(self):
        return self.name

    def set_name(self, name=None):
        if not name:
            self.name = 'image id:' + id(self)
            return
        self.name = name

    def cvtColor(self, method=cv2.COLOR_BGR2GRAY):
        self.img = cv2.cvtColor(self.img, method)

    def find_pattern_from_list(self, pat_list, cache=False):
        reg = None
        for pat in pat_list:
            reg = self.find_pattern(pat)
            if reg:
                break
        return reg

    def find_pattern(self, pattern,all=False):

        return pattern.pattern_finder(self, pattern,all=all)

        # Search for all occurence of pattern in source image


class App(object):
    def __init__(self, name='Clicker Heroes', width: int = None):
        print("init App")
        FindWindow.argtypes = [LPCWSTR, LPCWSTR]
        FindWindow.restype = HWND
        self.name = name
        self.window = Window(FindWindow(None, name))
        if width:
            self.window.resizeCliPropW(width)
            # FindWindow.argtypes = [ctypes.c_wchar_p,ctypes.c_wchar_p]
            # FindWindow.restype = ctypes.c_void_p

    def getWindow(self):
        return self.window


class SingletonMetaClass(type):
    def __init__(cls, name, bases, dict):
        super(SingletonMetaClass, cls) \
            .__init__(name, bases, dict)
        original_new = cls.__new__

        def my_new(cls, *args, **kwds):
            if cls.instance == None:
                cls.instance = \
                    original_new(cls, *args, **kwds)
            return cls.instance

        cls.instance = None
        cls.__new__ = staticmethod(my_new)


class Singleton(type):
    instance = None

    def __call__(cls, *args, **kw):
        if not cls.instance:
            cls.instance = super(Singleton, cls).__call__(*args, **kw)
        return cls.instance




class MouseClick:
    def __init__(self, window, x, y):
        self.hwnd = window.hwnd
        self.x = x
        self.y = y

    def apply(self):
        self.click(self.x, self.y)

    def click(self, x, y, park=True, cps=30):
        x = int(x)
        y = int(y)
        self.last_click_location = (x, y)
        tmp = (y << 16) | x
        delay = 1 / cps
        if park:
            delay /= 2

        err = 0
        err += SendMessage(self.hwnd, WM_LBUTTONDOWN, 0, tmp)
        time.sleep(delay)

        err += SendMessage(self.hwnd, WM_LBUTTONUP, 0, tmp)

        if park:
            x = 1
            y = 1
            tmp = (y << 16) | x
            time.sleep(delay)
            err += SendMessage(self.hwnd, WM_MOUSEMOVE, 0, tmp)

        if err > 0:
            return None
        return True

    def move(self, x, y, park=True, cps=30):
        l_x, ly = self.last_click_location
        x = int(x)
        y = int(y)
        tmp = (y << 16) | x

        delay = 1 / cps
        if park:
            delay /= 2

        err = 0
        err += SendMessage(self.hwnd, WM_LBUTTONDOWN, 0, tmp)
        time.sleep(delay)

        err += SendMessage(self.hwnd, WM_LBUTTONUP, 0, tmp)

        if park:
            x = 1
            y = 1
            tmp = (y << 16) | x
            time.sleep(delay)
            err += SendMessage(self.hwnd, WM_MOUSEMOVE, 0, tmp)

        if err > 0:
            return None
        return True


class MouseScroll:
    def __init__(self, window, direction):
        self.hwnd = window.hwnd
        self.direction = direction

    def apply(self):
        self.scroll(direction=self.direction)

    def scroll(self, direction, x=1, y=1, park=True, cps=30):
        tmp = (y << 16) | x
        delay = 1 / cps
        if park:
            delay /= 2

        err = 0
        err += SendMessage(self.hwnd, WM_MOUSEWHEEL,
                           (WHEEL_DELTA * direction) << 16, tmp)
        time.sleep(delay)
        if park:
            x = 1
            y = 1
            tmp = (y << 16) | x
            time.sleep(delay)
            err += SendMessage(self.hwnd, WM_MOUSEMOVE, 0, tmp)
        if err > 0:
            return None
        return True


class ClickerHeroes(metaclass=Singleton):
    # class ClickerHeroes(App):
    #    __metaclass__ = Singleton
    def __init__(self, lock, width: int = None) -> None:
        if DEBUG:
            print("init ClickerHeroes")

        name = 'Clicker Heroes'
        self.name = name
        self.window = Window(FindWindow(None, name), lock)
        if width:
            self.window.resizeCliPropW(width)

        self.lock = lock

        self.fish_time = -1000000
        self.newyear = -1000000
        self.farm_mode_start_time = -1000000
        self.ascend_time = 0
        self.ascend_checker_time = 0
        self.got_heroes_souls = False
        self.relic_ooze_collected = False
        self.reindex_heroes_list_time = 0
        self.patterns = {}
        self.menus = {}
        self.hero_patterns_location_cache = {}
        self.patterns_location_cache = {}
        self.patterns_cache = {}
        self.click_monster_location = None
        self.starter_clicks = True
        self.lvlup_all_heroes_time = 0
        self.boss_time = None
        self.boss_check_time = 0
        self.levels_region = None
        self.levels_region_scrshot = None
        self.progress_button_time = -1000000
        self.farm_mode_start_time = -1000000
        self.cache_state = False
        self.reindex_heroes_list_time = -1000000
        self.skills_upgrades_time = 0

        width, height = self.window.get_size()

        sss = MouseClick(self.window, 1, 1)
        scale = 1

        if width > height * 16.0 / 9:
            scale = height / (1600.0 * 9 / 16)
        if height > width * 9.0 / 16:
            scale = width / 1600.0
        self.script_path=os.path.realpath(__file__)
        self.script_dir=os.path.dirname(self.script_path)
        self.stats_dir=os.path.join(self.script_dir,STATS_DIR)
        self.patterns_path=os.path.join(self.script_dir,PATTERNS_DIR)
        self.load_patterns(self.patterns_path, self.patterns, scale)
        self.hero_patterns_location_cache = {}
        for menu_name in ('heroes', 'ancients'):
            self.menus[menu_name] = {}
            # self.menus[menu_name]['sorted_heroes_list'] = self.load_sorted_heroes_list(menu_name)
            self.menus[menu_name]['sorted_heroes_list'] = self.load_container(menu_name, "sorted_heroes_list", [])
            self.menus[menu_name]['sb_min_position'] = None
            self.menus[menu_name]['sb_max_position'] = None
            self.menus[menu_name]['sb_position'] = 0
            self.menus[menu_name]['last_available_hero'] = None
            self.menus[menu_name]['max_seen_hero'] = None
            self.menus[menu_name]['heroes_list'] = None
            self.menus[menu_name]['visible_heroes_cache'] = None
            # self.menus[menu_name]['hero_level'] = self.load_heroes_levels(menu_name)
            self.menus[menu_name]['hero_level'] = self.load_container(menu_name, "hero_level", {})
            self.menus[menu_name]['heroes_upgraded_list'] = self.load_container(menu_name,
                                                                                      "heroes_upgraded_list",
                                                                                      [])
            self.menus[menu_name]['last_ascend_seen_heroes']=set()
        self.window.makeScreenshotClientAreaRegion()
        # self.set_monster_click_location()

    def do(self):
        self.screenShot = self.window.getScreenshot()
        self.lvlup_top_heroes()
        # self.buyHeroesUpgrade()

        self.lvl_progress()
        # if self.ascensionNeed():

    #            self.ascend()
    #            self.lvlUpAncient()
    #        if self.transcendNeed():
    #            self.trascend()
    #            self.lvlUpOutsiders()

    # Loading image patterns structure in self.patterns
    def get_sorted_heroes_list(self, menu_name):
        return self.menus[menu_name]['sorted_heroes_list']

    def load_patterns(self, path, patterns, scale):
        bbb = patterns
        for root, dirs, files in os.walk(path):
            for fn in files:
                name, ext = os.path.splitext(os.path.basename(fn))
                nm = root[root.find(path) + len(path):]
                # Change os path sepatator to /
                nm = re.sub(re.escape(os.sep), '/', os.path.join(nm, name))
                if 'lvlup_' in nm:
                    find_in_func = find_lvlup
                elif 'button_progression' in nm:
                    find_in_func = find_single_grey_90
                elif '_c' in nm and 'heroes_skills' in nm:
                    # find_in_func = find_checked_skills
                    find_in_func = find_pattern_hist

                else:
                    find_in_func = find_single_grey
                img = Image.fromFile(path=os.path.join(root, fn), name=name, find_in_func=find_in_func)
                img.resize(scale)
                bbb[nm] = img

        pass

    def find_pattern(self, pat):
        return self.find_pattern_cached(pat)

    def find_pattern_from_list(self, pat_list, cache=True,all=False):
        regions = []
        for pat in pat_list:
            if cache:
                reg = self.find_pattern_cached(pat,all=all)
            else:
                reg = self.window.getScreenshot().find_pattern(pat,all=all)

            if reg:
                regions.extend(reg)
                if not all:
                    break
        return regions

    def find_pattern_reg_name(self, pat_list):
        reg = None
        reg_name = []
        for pat in pat_list:
            regs = self.find_pattern(pat)
            if regs:
                for r in regs:
                    reg_name.append((r, pat.get_name()))
        return reg_name

    def find_pattern_reg_name_single(self, reg, pat_list):
        reg_name = None
        for pat in pat_list:
            regs = self.window.getScreenshot(reg).find_pattern(pat)
            if regs:
                regs = regs[0]
                reg_name = (regs, pat.get_name())
                break
        # if not reg_name:
        #     return None
        return reg_name

    def find_pattern_cached(self, pat,all=False):
        # pat_id = id(pat)

        pat_id = pat.get_name()
        if pat_id not in self.patterns_location_cache.keys():
            self.patterns_location_cache[pat_id] = {}
        # pattern location cache
        plc = self.patterns_location_cache[pat_id]
        regions = []
        if plc:
            # print("find_pattern_cached: Pattern %s has %s entries in cache location" % (pat.get_name(), len(plc)))
            # Quickly scan pattern location cache
            cnt = 0
            for cached_location in plc.keys():
                reg = self.window.getScreenshot(cached_location).find_pattern(pat,all=False)
                cnt += 1
                # If location exist in cache and pattern is on screen add location to retrun
                if reg:
                    # print("find_pattern_cached: Cache hit!! Pattern %s" % (pat.get_name()))
                    plc[cached_location] += 1
                    if DEBUG and cnt > 1:
                        print("find_pattern_cached: Pattern %s : Cache hit on %s cache entry" % (pat_id, cnt))
                    regions.append(cached_location)
                    break

        # If pattern dont exists on locations from cache scan the whole screen and cache it
        if not regions:
            # Scan the whole screen
            # print("find_pattern_cached: Cache missed!! Searching for %s " % (pat.get_name()))
            reg = self.window.getScreenshot().find_pattern(pat,all=all)

            # print("find_pattern_cached: Found reg %s " % (reg))
            # If location found add it to cache and
            if reg:
                # hit_count = [1] * len(reg)
                # cache_entry = zip(reg, hit_count)
                plc = self.patterns_location_cache[pat_id]
                plc.update(dict.fromkeys(reg, 1))
                regions.extend(reg)
            else:
                # Nothing found in cache and on screen
                return None
        if plc:
            if len(plc) != 1:
                # Sort by cache hit count
                plc = OrderedDict(sorted(plc.items(), key=lambda t: t[1], reverse=True))
            self.patterns_location_cache[pat_id] = plc
            # print(plc)
        return regions

    def scroll_to_last_available_hero(self, menu_name):
        self.scroll_to_position(menu_name, self.menus[menu_name]['sorted_heroes_list'])
        return

    def get_prev_hero_name(self, menu_name, hero_name):
        if hero_name is None:
            return None
        unsorted_heroes_list = self.get_unsorted_hero_list(menu_name)
        sorted_heroes_list = self.get_sorted_heroes_list(menu_name)
        # Previous hero index
        try:
            if sorted_heroes_list:
                hindex = sorted_heroes_list.index(hero_name) - 1
                if hindex >= 0:
                    # Can definitely be deterrmine previous heroe name
                    ret_hlist = [sorted_heroes_list[hindex]]
                else:
                    # Return heroes that can be possible be previous in list and dont sits in sorted_heroes_list
                    # Hero oredered list doest contains hero_name so we return all heroes that dont sit in hol
                    # and dont equal to hero_name
                    # ret_hlist = [name for name in unsorted_heroes_list if name not in sorted_heroes_list and name != hero_name]
                    ret_hlist = [name for name in unsorted_heroes_list if name != hero_name]
            else:
                # Hero ordered list is empty so return all heroes from hero list except hero_name
                ret_hlist = [name for name in unsorted_heroes_list if name != hero_name]
        except ValueError as e:
            ret_hlist = None
        return ret_hlist

    def get_next_hero_name(self, menu_name, hero_name):
        if hero_name is None:
            return None
        unsorted_heroes_list = self.get_unsorted_hero_list(menu_name)
        sorted_heroes_list = self.get_sorted_heroes_list(menu_name)
        ret_hlist = None
        # Next hero index
        try:
            if sorted_heroes_list:
                hindex = sorted_heroes_list.index(hero_name) + 1
                if hindex >= len(sorted_heroes_list):
                    # Return heroes that can be possible be next in list and dont sits in sorted_heroes_list
                    # Hero oredered list doest contains hero_name so we return all heroes that dont sit in hol
                    # and dont equal to hero_name
                    # ret_hlist = [name for name in unsorted_heroes_list if name not in sorted_heroes_list and name != hero_name]
                    ret_hlist = [name for name in unsorted_heroes_list if name != hero_name]
                else:
                    # Can definitely be determine next heroes name
                    ret_hlist = [sorted_heroes_list[hindex]]
            else:
                # Hero ordered list is empty so return all heroes from hero list except hero_name
                ret_hlist = [name for name in unsorted_heroes_list if name != hero_name]
        except ValueError as e:
            ret_hlist = None

        return ret_hlist

    def get_max_seen_hero(self, menu_name):
        return self.menus[menu_name]['max_seen_hero']

    def set_max_seen_hero(self, menu_name, hero_name):
        self.menus[menu_name]['max_seen_hero'] = hero_name

    def lvlup_all_heroes(self, menu_name, max_level=200, timer=180):
        self.window.makeScreenshotClientAreaRegion()
        curr_time = time.clock()
        if curr_time - self.lvlup_all_heroes_time < timer:
            return None

        self.lvlup_all_heroes_time = curr_time
        sorted_hero_list = self.get_sorted_heroes_list(menu_name)
        if sorted_hero_list is None:
            return None

        last_available_hero = self.get_last_available_hero(menu_name)
        if last_available_hero:
            last_available_hero_index = sorted_hero_list.index(last_available_hero)
        else:
            return None

        heroes_to_lvlup = [hero_name for hero_name in sorted_hero_list if
                           self.get_hero_level(menu_name, hero_name) < max_level and sorted_hero_list.index(
                               hero_name) <= last_available_hero_index]

        for hero_name in heroes_to_lvlup:
            self.lvlup_hero(menu_name, hero_name, max_level=max_level)
        return
            ###Buy heroes skill except ascension
            # hero_reg = self.scroll_to_hero(menu_name, hero_name)
            # hero_reg_scr = self.window.makeScreenshotClientAreaRegion(hero_reg)
            # skills_reg = hero_reg_scr.find_pattern_from_list(self.get_pattern('heroes_skills', '%s_c' % hero_name))
            # if skills_reg:
            #     continue
            #
            # if hero_name == 'amenhotep':
            #     ascend_skill_reg = hero_reg_scr.find_pattern_from_list(
            #         self.get_pattern('heroes_skills', 'amenhotep_ascend'),
            #         cache=False)
            #     if ascend_skill_reg:
            #         ascend_skill_reg = ascend_skill_reg[0]
            #     else:
            #         continue
            # else:
            #     ascend_skill_reg = None
            # button_edge_reg = hero_reg_scr.find_pattern_from_list(self.get_pattern('heroes_button', 'edge_'),
            #                                                       cache=False)
            # if button_edge_reg is None:
            #     continue
            # button_edge_reg = button_edge_reg[0]
            # hero_name_reg = hero_reg_scr.find_pattern_from_list(self.get_pattern(menu_name, hero_name))
            # if hero_name_reg is None:
            #     continue
            # hero_name_reg = hero_name_reg[0]
            # skills_reg_left_x, skills_reg_left_y = button_edge_reg.center().get_xy()
            # skills_reg_right_x = hero_name_reg.getRight()
            # y = hero_reg.getTop() + skills_reg_left_y
            # for i in range(100):
            #     x = hero_reg.getLeft() + skills_reg_left_x + int(
            #         random.random() * (skills_reg_right_x - skills_reg_left_x))
            #     if ascend_skill_reg and ascend_skill_reg.contains((x - hero_reg.getLeft(), y - hero_reg.getTop())):
            #         continue
            #     hero_reg_scr = self.window.makeScreenshotClientAreaRegion(hero_reg)
            #     cv2.imshow("hero_reg_scr", hero_reg_scr.get_array())
            #     cv2.waitKey(50)
            #     # skills_reg = hero_reg_scr.find_pattern_from_list(self.get_pattern('heroes_skills', '%s_c' % hero_name))
            #     # if skills_reg:
            #     #     break
            #     self.window.click(x, y, cps=5)

    def lvlup_top_heroes(self, menu_name, dist=0):
        self.window.makeScreenshotClientAreaRegion()
        img = self.window.getScreenshot().get_resized_copy(w=300).get_array()
        cv2.imshow('lvlup_top_heroes:img', img)
        cv2.waitKey(50)
        hero_name = self.get_last_available_hero(menu_name)
        if hero_name is None:
            return None
        i = 0
        while i <= dist:
            if hero_name:
                res = self.lvlup_hero(menu_name, hero_name)
            hero_lst = self.get_prev_hero_name(menu_name, hero_name)
            if hero_lst:
                hero_name = hero_lst[0]
            else:
                break
            i += 1

    def set_last_available_hero(self, menu_name, hero_name):
        self.menus[menu_name]['last_available_hero'] = hero_name

    def get_last_available_hero(self, menu_name):
        hol = self.get_sorted_heroes_list(menu_name)
        hol_length = len(hol)
        if hol is None:
            return None
        lah = None
        # pah = None
        lahp = self.menus[menu_name]['last_available_hero']
        if lahp:
            # Check that lahp is the last hero in the list
            if lahp == hol[-1]:
                return lahp
            else:
                next_lah_index = hol.index(lahp) + 1
                # pah = self.get_next_hero_name(menu_name, lahp)
        else:
            next_lah_index = 0

        max_seen_hero = self.get_max_seen_hero(menu_name)
        if not max_seen_hero:
            return None
        max_seen_hero_index = hol.index(max_seen_hero) + 1
        if max_seen_hero_index >= next_lah_index:
            to_check_heroes = hol[next_lah_index:max_seen_hero_index]
        for h in reversed(to_check_heroes):
            reg = self.scroll_to_hero(menu_name, h)
            if reg is None:
                return None
            if self.is_hero_lvlup_button_active(reg):
                lah = h
                cv2.imshow("get_last_available_hero:lah_reg", self.window.getScreenshot(reg).get_array())
                cv2.waitKey(50)
                break
        if lah:
            lah_index = hol.index(lah)
        else:
            lah_index = 0
        if lah_index >= next_lah_index:
            self.set_last_available_hero(menu_name, lah)
        return self.menus[menu_name]['last_available_hero']

    def find_hero_lvlup_button(self, hero_reg):
        if hero_reg is None:
            return None
        cv2.imshow("find_hero_lvlup_button:hero_reg", self.window.getScreenshot(hero_reg).get_array())
        cv2.waitKey(50)

        return self.find_lvlup_button(hero_reg)

    def find_hero_level_reg(self, reg):
        if reg is None:
            return None
        level_mark_patterns = self.get_pattern('heroes_button', 'level_mark')
        reg_name = self.find_pattern_reg_name_single(reg, level_mark_patterns)
        if reg_name is None:
            return None
        # Absolute region of level mark
        level_mark_reg = reg_name[0]
        loc1 = Location(reg.getLeft() + level_mark_reg.getLeft(), reg.getTop() + level_mark_reg.getTop())
        loc2 = Location(reg.getRight(), reg.getTop() + level_mark_reg.getBottom())
        level_mark_reg = Region.from2Location(loc1, loc2)

        return level_mark_reg

    ###################################
    # def find_hero_region(self, menu_name, hero_name):
    #     reg = self.scroll_to_hero(menu_name, hero_name)
    #     return reg
    ###################################
    def find_lvlup_button(self, reg):
        button_patterns = self.get_pattern('heroes_button', 'lvlup_')
        reg_name = self.find_pattern_reg_name_single(reg, button_patterns)
        if reg_name is None:
            return None
        # Absolute region
        reg = reg_name[0] + (reg.x, reg.y)
        cv2.imshow("find_lvlup_button:reg_name[0]", self.window.getScreenshot(reg).get_array())
        cv2.waitKey(50)
        butt_reg_name = (reg, reg_name[1])
        if 'hire_inactive' in butt_reg_name[1]:
            # if all(x in butt_reg_name[1] for x in ['inactive', 'hire']):
            status = False
        else:
            status = True
        return (butt_reg_name[0], status)

    def find_level_reg(self, reg):
        return

    def is_hero_lvlup_button_active(self, hero_reg):
        self.window.makeScreenshotClientAreaRegion()
        lvl_button = self.find_hero_lvlup_button(hero_reg)
        if lvl_button is None:
            return None
        status = lvl_button[1]
        return status

    def get_hero_level(self, menu_name, hero_name):
        hero_level_dict = self.menus[menu_name]['hero_level']
        if hero_name not in hero_level_dict.keys():
            hero_level_dict[hero_name] = 0
        return hero_level_dict[hero_name]

    def set_hero_level(self, menu_name, hero_name, level):
        hero_level_dict = self.menus[menu_name]['hero_level']
        if hero_name not in hero_level_dict.keys():
            hero_level_dict[hero_name] = 0
        hero_level_dict[hero_name] = level

    def add_hero_level(self, menu_name, hero_name, level):
        hero_level_dict = self.menus[menu_name]['hero_level']
        if hero_name not in hero_level_dict.keys():
            hero_level_dict[hero_name] = 0
        hero_level_dict[hero_name] += level

    def get_heroes_level_dict(self, menu_name):
        return self.menus[menu_name]['hero_level']

    # def save_heroes_levels(self, menu_name, hld):
    #     try:
    #         hld_filename = STATS_DIR + '/%s_heroes_levels.dat' % menu_name
    #         with tempfile.NamedTemporaryFile(mode='w+t', delete=False, dir=STATS_DIR) as temp_file:
    #             json.dump(hld, temp_file)
    #         if os.path.isfile(hld_filename):
    #             shutil.copy(hld_filename, hld_filename + '.bck')
    #
    #         os.replace(temp_file.name, hld_filename)
    #     except OSError:
    #         raise

    def save_sorted_heroes_list(self, menu_name, shl):
        try:
            shl_filename = os.path.join(self.stats_dir,'%s_sorted_heroes_list.dat' % menu_name)
            with tempfile.NamedTemporaryFile(mode='w+t', delete=False, dir=STATS_DIR) as temp_file:
                json.dump(shl, temp_file)
            if os.path.isfile(shl_filename):
                shutil.copy(shl_filename, shl_filename + '.bck')
            os.replace(temp_file.name, shl_filename)
        except OSError:
            raise

    def load_sorted_heroes_list(self, menu_name):
        try:
            fn = STATS_DIR + '/%s_sorted_heroes_list.dat' % menu_name
            with open(fn, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            return []

    def save_container(self, menu_name, container_name, container):
        try:
            shl_filename = os.path.join(self.stats_dir, '%s_%s' % (menu_name, container_name))
            with tempfile.NamedTemporaryFile(mode='w+t', delete=False, dir=self.stats_dir) as temp_file:
                json.dump(container, temp_file)
            if os.path.isfile(shl_filename):
                shutil.copy(shl_filename, shl_filename + '.bck')
            os.replace(temp_file.name, shl_filename)
        except OSError:
            raise

    def load_container(self, menu_name, container_name, default_container):
        try:
            fn = os.path.join(self.stats_dir, '%s_%s' % (menu_name, container_name))
            # fn = STATS_DIR + '/%s_%s' % (menu_name, container_name)
            with open(fn, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            return default_container

    def save_heroes_levels(self, menu_name, hld):
        try:
            hld_filename = STATS_DIR + '/%s_heroes_levels.dat' % menu_name
            with tempfile.NamedTemporaryFile(mode='w+t', delete=False, dir=STATS_DIR) as temp_file:
                json.dump(hld, temp_file)
            if os.path.isfile(hld_filename):
                shutil.copy(hld_filename, hld_filename + '.bck')

            os.replace(temp_file.name, hld_filename)
        except OSError:
            raise

    def load_heroes_levels(self, menu_name):
        try:
            fn = STATS_DIR + '/%s_heroes_levels.dat' % menu_name
            with open(fn, 'r') as f:
                return json.load(f)
        except FileNotFoundError:
            return {}

    def lvlup_hero(self, menu_name, hero_name, lvl_count=None, max_level=None):
        self.open_menu(menu_name)
        hero_reg = self.scroll_to_hero(menu_name, hero_name=hero_name)
        # hero_reg_scr=    self.window.makeScreenshotClientAreaRegion(hero_reg)
        # button_edge_reg=hero_reg_scr.find_pattern(self.get_pattern('heroes_button','edge_'))
        # skills_reg_left_x,skills_reg_left_y=button_edge_reg.center().get_xy()
        # hero_name_reg=hero_reg_scr.find_pattern(self.get_pattern(menu_name,hero_name))
        # skills_reg_right_x=hero_name_reg.getRight()
        # for i in range(100):
        #     x=skills_reg_left_x+int(random.random()*(skills_reg_right_x-skills_reg_left_x))
        #     y=skills_reg_left_y
        #     self.window.click(hero_reg.getRight()+x,hero_reg.getTop()+y)

        if hero_reg is None:
            return None
        button = self.find_hero_lvlup_button(hero_reg)

        if button is None:
            return None

        hero_level = self.get_hero_level(menu_name, hero_name)
        levelup_button = button[0]
        if lvl_count is None:
            lvl_count = 1000 * 1000 * 1000
        if max_level:
            lvl_count = max_level - hero_level
        time_1 = time.clock()
        start_time = time.clock()
        cnt = 0
        hold_key = 'shift'
        if max_level is None:
            hold_key = 'q'

        self.window.pressAndHoldKey(hold_key)
        while True:
            # time.sleep(0.2)
            # if menu_name == 'heroes':
            # For speed make screenshot of lvlup button area
            time_chk = time.clock()
            # delay = 0.01
            # max = 0
            # while max == 0 and delay<=1: # time.clock() - time_chk < 0.3:
            #     scrshot = self.window.makeScreenshotClientAreaRegion(reg)
            #     # Quick and dirty check for active button
            #     max = scrshot.get_threshold(128, 255).get_array().max()
            #
            #     time.sleep(delay)
            #     delay *= 2
            # reg, status = self.find_hero_lvlup_button(menu_name, hero_name)
            self.window.makeScreenshotClientAreaRegion()
            scr_levelup = self.window.makeScreenshotClientAreaRegion(levelup_button)
            max = scr_levelup.get_threshold(128, 255).get_array().max()
            if max == 0:
                break
            level_reg = self.find_hero_level_reg(hero_reg)
            if level_reg is None:
                check_reg = levelup_button
                pattern_finder = find_lvlup
            else:
                check_reg = level_reg
                pattern_finder = find_level

            scr_level_before = self.window.makeScreenshotClientAreaRegion(check_reg)  # .get_threshold(235,255)
            self.click_region(levelup_button)
            delay = 0.01
            total_delay = 0
            # Wait a little after click applied
            while total_delay <= 1:  # time.clock() - time_chk < 0.3:
                time.sleep(delay)
                total_delay += delay
                scr_level_after = self.window.makeScreenshotClientAreaRegion(check_reg)  # .get_threshold(235,255)
                scr_level_after.set_pattern_finder(pattern_finder)
                cv2.imshow('scr_level_before', scr_level_before.get_array())
                cv2.imshow('scr_level_after', scr_level_after.get_array())
                cv2.waitKey(25)
                # comp=cv2.compare(scr_level_before.get_array(),scr_level_after.get_array(),cv2.CMP_EQ)
                # comp = cv2.bitwise_xor(scr_level_before.get_array(), scr_level_after.get_array())
                # if comp.min()==0:
                if not scr_level_before.find_pattern(scr_level_after):
                    break
                delay *= 2

            if total_delay > 1 and check_reg == level_reg:
                break
            cnt += 10
            if time.clock() - start_time > 120 or cnt >= lvl_count:
                break

        self.window.releaseKey(hold_key)
        # self.window.move_mouse(y=10)
        time.sleep(0.5)
        time_2 = time.clock()
        # self.menus[menu_name][hero_name]['lvl'] += 1
        self.add_hero_level(menu_name, hero_name, cnt)
        if cnt == 0:
            return None
        if DEBUG:
            print("lvlup_hero:lvl/sec=%s" % (cnt / (time_2 - time_1)))

        # self.save_heroes_levels(menu_name, self.get_heroes_level_dict(menu_name))
        self.save_container(menu_name, 'hero_level', self.menus[menu_name]['hero_level'])

        return cnt

    def click_location(self, loc, refresh=False):
        # x, y = loc.get_xy()
        # mouse_event = MouseClick(self.window, x, y)
        # # self.mouse_event_queue.put((mouse_event, self.mp_event))
        # l=list()
        # # self.mouse_event_queue.put(mouse_event)
        # self.mouse_event_queue.put(l)
        # # self.mouse_event_queue.put('123123123')
        # self.mp_event.wait()

        return  self.window.click_location(loc, refresh=refresh)



    def click_region(self, reg, refresh=False):

        # x, y = reg.center().get_xy()
        # mouse_event = MouseClick(self.window, x, y)
        # self.mouse_event_queue.put((mouse_event, self.mp_event))
        # self.mp_event.wait()
        ret = self.window.click_region(reg, refresh=refresh)
        return ret

    def scrollDownMenu(self, name):
        self.menus[name]['scrollPosition'] += 1
        scrPos = self.menus[name]['scrollPosition']
        if scrPos > self.menus[name]['maxScrollPosition']:
            self.menus[name]['maxScrollPosition'] = scrPos

    def get_pattern_old(self, menu_name, pattern_name):
        if pattern_name not in self.patterns[menu_name].keys():
            return None
        return self.patterns[menu_name][pattern_name]

    def get_pattern(self, menu_name, pattern_name):
        path = '/%s/%s' % (menu_name, pattern_name)
        if path in self.patterns_cache.keys():
            patterns_list = self.patterns_cache[path]
        else:
            patterns_list = [self.patterns[key] for key in self.patterns.keys() if key.startswith(path)]
            self.patterns_cache[path] = patterns_list
        return patterns_list

    def find_hero_location_old(self, menu_name, hero_name):
        if hero_name not in self.hero_patterns_location_cache[menu_name]:
            self.hero_patterns_location_cache[menu_name][hero_name] = []
        # hero pattern location cache
        hplc = self.hero_patterns_location_cache[menu_name][hero_name]
        for cached_location in hplc:
            if cached_location is None:
                break
            pat = self.get_pattern(menu_name, hero_name)
            for img in pat:
                if self.window.getScreenshot(cached_location).find_pattern(img) is not None:
                    return cached_location
        location = None
        for pat in self.get_pattern(menu_name, hero_name):
            location = self.window.getScreenshot().find_pattern(pat)
            if location not in hplc and location is not None:
                hplc.append(location)
                break
        return location

    def find_hero_region(self, menu_name, hero_name):
        pat = self.get_pattern(menu_name, hero_name)
        return self.find_pattern_from_list(pat)

    def get_last_hero(self, menu_name):
        return self.get_sorted_heroes_list(menu_name)[-1]

    def get_hero_list(self, menu_name):
        path = '/%s/' % (menu_name)
        #
        hl = self.menus[menu_name]['heroes_list']
        if hl is None:
            hl = set(
                [key.rpartition('/')[2].rpartition('_')[0] for key in self.patterns.keys() if key.startswith(path)])
            self.menus[menu_name]['heroes_list'] = hl
        return hl

    def get_unsorted_hero_list(self, menu_name):
        hero_list = self.get_hero_list(menu_name)
        sorted_heroes_list = self.get_sorted_heroes_list(menu_name)
        return [name for name in hero_list if name not in sorted_heroes_list]

    def get_visible_heroes_cached_old(self, menu_name):
        vhc = self.menus[menu_name]['visible_heroes_cache']
        sp = self.get_scroll_pos(menu_name)
        if sp not in vhc.keys():
            return None
        return vhc[sp]

    def cache_visible_heroes_old(self, menu_name: str, hero_name_list):
        vhc = self.menus[menu_name]['visible_heroes_cache']
        sp = self.get_scroll_pos(menu_name)
        if sp not in vhc.keys():
            vhc[sp] = set()
        # vhc[sp].update(hero_name_list)
        vhc[sp] = hero_name_list

    def get_visible_heroes_cached(self, menu_name):
        vhc = self.menus[menu_name]['visible_heroes_cache']
        return vhc

    def cache_visible_heroes(self, menu_name: str, hero_name_list):
        self.menus[menu_name]['visible_heroes_cache'] = hero_name_list
        self.validate_cache_state()

    def get_visible_heroes_old(self, menu_name):
        self.open_menu(menu_name)
        visible_heroes = []
        hl = self.get_visible_heroes_cached(menu_name)
        loop = 1
        while not visible_heroes:
            if not hl or loop > 1:
                hl = self.get_hero_list(menu_name)
                if DEBUG:
                    print("get_visible_heroes: visible_heroes_cache missed")
            for name in hl:
                reg = self.find_hero_region(menu_name, name)
                if reg:
                    visible_heroes.append((name, reg[0]))
            loop += 1
        visible_heroes_names = list(zip(*visible_heroes))[0]
        self.cache_visible_heroes(menu_name, visible_heroes_names)
        # Sort visible heroes list by y position
        return sorted(visible_heroes, key=lambda x: x[1].y)

    def get_last_ascend_seen_heroes(self,menu_name):
        #
        #
        # shl=self.get_sorted_heroes_list(menu_name)
        # if not shl:
        #     return None
        #
        # hl=self.get_hero_list(menu_name)
        # if not hl:
        #     return None
        # msh=self.get_max_seen_hero(menu_name)
        # if not msh:
        #     return None
        #
        # mshi=hl.index(msh)`

        # return shl[:hl.index(self.get_max_seen_hero(menu_name))]
        return self.menus[menu_name]['last_ascend_seen_heroes']
    def add_last_ascend_seen_heroes(self,menu_name,hero_name):
        self.menus[menu_name]['last_ascend_seen_heroes'].update(hero_name)

    def get_visible_heroes(self, menu_name, number_of_vh=MAX_NUMBER_OF_VISIBLE_HEROES):
        self.open_menu(menu_name)
        visible_heroes = []
        hl = self.get_hero_list(menu_name)
        hlc = self.get_visible_heroes_cached(menu_name)
        hol = self.get_sorted_heroes_list(menu_name)
        check_remain_heroes = True
        cache_state = self.get_cache_state()

        if hlc:
            # if self.cache_state_is_valid():
            #     return hlc
            # Get hero name list from cache
            hero_name_cached = list(zip(*hlc))[0]
            for name in hero_name_cached:
                reg = self.find_hero_region(menu_name, name)
                if reg:
                    visible_heroes.append((name, reg[0]))
                if len(visible_heroes) >= number_of_vh:
                    check_remain_heroes = False
                    break

            visible_heroes = sorted(visible_heroes, key=lambda x: x[1].y)

        if visible_heroes and check_remain_heroes:
            top_hero_name = visible_heroes[0][0]
            bottom_hero_name = visible_heroes[-1][0]
            for dir in [(top_hero_name, self.get_prev_hero_name), (bottom_hero_name, self.get_next_hero_name)]:
                name = dir[0]
                func = dir[1]
                can_change_edge = False
                if check_remain_heroes:
                    while 1:
                        # name_list = self.get_prev_hero_name(menu_name, name)
                        pass
                        name = func(menu_name, name)
                        if not name:
                            break
                        pass
                        for n in name:
                            reg = self.find_hero_region(menu_name, n)
                            if reg:
                                visible_heroes.append((n, reg[0]))
                            else:
                                can_change_edge = True
                            if len(visible_heroes) >= number_of_vh:
                                check_remain_heroes = False
                                break
                        if len(name) > 1 or not check_remain_heroes:
                            break
                        if len(name) == 1 and can_change_edge == True:
                            break
                        if len(name) == 1:
                            name = name[0]





                            # name_list = self.get_prev_hero_name(menu_name, name)
                            # if name_list and check_remain_heroes:
                            #     for name in name_list:
                            #         reg = self.find_hero_region(menu_name, name)
                            #         if reg:
                            #             visible_heroes.append((name, reg[0]))
                            #         if len(visible_heroes) >= number_of_vh:
                            #             check_remain_heroes = False
                            #             break

                            # name = bhn
                            # while 1:
                            #     name_list = self.get_next_hero_name(menu_name, name)
                            #     for name in name_list:
                            #         reg = self.find_hero_region(menu_name, name)
                            #         if reg:
                            #             visible_heroes.append((name, reg[0]))
                            #         if len(visible_heroes) >= number_of_vh:
                            #             check_remain_heroes = False
                            #             break
                            #     if len(name_list)>1:
                            #         break

        if not visible_heroes:
            name_list = hl
            if name_list and check_remain_heroes:
                for name in name_list:
                    reg = self.find_hero_region(menu_name, name)
                    if reg:
                        visible_heroes.append((name, reg[0]))
                    if len(visible_heroes) >= number_of_vh:
                        check_remain_heroes = False
                        break
        visible_heroes = set(visible_heroes)
        visible_heroes = sorted(visible_heroes, key=lambda x: x[1].y)
        if visible_heroes:
            visible_heroes_names = list(zip(*visible_heroes))[0]
            self.add_last_ascend_seen_heroes(menu_name, visible_heroes_names)

            self.cache_visible_heroes(menu_name, visible_heroes)
        # Sort visible heroes list by y position
        # self.add_last_ascend_seen_heroes( menu_name, visible_heroes_names)
        return visible_heroes

    def set_max_scroll_position(self, menu_name, pos):
        self.menus[menu_name]['sb_max_position'] = pos

    def set_min_scroll_position(self, menu_name, pos):
        self.menus[menu_name]['sb_min_position'] = pos

    def get_scroll_pos(self, menu_name):
        sp = self.menus[menu_name]['sb_position']
        # spx = self.get_scroll_max_pos(menu_name)
        # spm = self.get_scroll_min_pos(menu_name)
        # if spm  and sp < spm:
        #     return spm
        # if spx and sp > spx:
        #     return spx
        return sp

    def set_scroll_pos(self, menu_name, sp):
        self.menus[menu_name]['sb_position'] = sp

    def reindex_heroes_list(self, menu_name, reindex_timer=30):
        self.window.makeScreenshotClientAreaRegion()
        img = self.window.getScreenshot().get_resized_copy(w=300).get_array()
        cv2.imshow('reindex_heroes_list:img', img)
        cv2.waitKey(50)
        curr_time = time.clock()
        if curr_time - self.reindex_heroes_list_time < reindex_timer:
            return False
        self.reindex_heroes_list_time = curr_time

        self.open_menu(menu_name)
        if self.get_sorted_heroes_list(menu_name) is None:
            dir_list = [WHEEL_UP, WHEEL_DOWN]
        else:
            dir_list = [WHEEL_DOWN]
            # self.scroll_to_last(menu_name)

        # dir_list = [WHEEL_UP, WHEEL_DOWN]
        # Start scrolling to find location of heroes
        for direction in dir_list:
            visible_heroes = None
            bug_scroll_heroes = None
            while True:
                # if direction == WHEEL_UP:
                #     op_dir=WHEEL_DOWN
                # else:
                #     op_dir=WHEEL_UP
                #
                # self.scroll_menu(menu_name, op_dir)
                # self.scroll_menu(menu_name, direction)
                prev_vis_heroes = visible_heroes
                visible_heroes = self.get_visible_heroes(menu_name)
                if not visible_heroes:
                    return None
                # if (visible_heroes and prev_vis_heroes):
                #     print("reindex_heroes_list: set==set %s" % (set(visible_heroes) == set(prev_vis_heroes)))
                if (visible_heroes and prev_vis_heroes) and set(visible_heroes) == set(prev_vis_heroes):
                    if direction == WHEEL_DOWN:
                        self.scroll_menu(menu_name, WHEEL_UP)
                        self.scroll_menu(menu_name, WHEEL_DOWN)
                        bug_scroll_heroes = self.get_visible_heroes(menu_name)
                        if bug_scroll_heroes == None:
                            return None
                        if set(visible_heroes) != set(bug_scroll_heroes):
                            continue

                    if direction == WHEEL_DOWN:
                        self.set_scroll_pos(menu_name, self.get_scroll_pos(menu_name) - 1)
                        self.set_max_scroll_position(menu_name, self.get_scroll_pos(menu_name))
                    else:
                        self.set_scroll_pos(menu_name, self.get_scroll_pos(menu_name) + 1)
                        self.set_min_scroll_position(menu_name, self.get_scroll_pos(menu_name))
                    break
                hol = self.menus[menu_name]['sorted_heroes_list']
                visible_heroes_names = list(zip(*visible_heroes))[0]

                if direction == WHEEL_UP:
                    # Adding heroes in front of sorted_heroes_list
                    hol[0:0] = [item for item in visible_heroes_names if item not in hol]
                else:
                    # Adding heroes in the end of of sorted_heroes_list
                    hol.extend([item for item in visible_heroes_names if item not in hol])
                local_max_seen_hero = visible_heroes_names[-1]
                global_max_seen_hero = self.get_max_seen_hero(menu_name)
                if global_max_seen_hero:
                    if hol.index(local_max_seen_hero) > hol.index(global_max_seen_hero):
                        self.set_max_seen_hero(menu_name, local_max_seen_hero)
                else:
                    self.set_max_seen_hero(menu_name, local_max_seen_hero)
                # Check if we need to scroll
                # if self.find_pattern_from_list(self.get_pattern('main', 'scroll_up')):
                self.scroll_menu(menu_name, direction)

                # else:
                #     # Just make screenshot
                #     self.window.makeScreenshotClientAreaRegion()
                self.invalidate_cache_state()
            self.validate_cache_state()
        # self.save_sorted_heroes_list(menu_name, shl=self.menus[menu_name]['sorted_heroes_list'])
        self.save_container(menu_name, 'sorted_heroes_list', self.menus[menu_name]['sorted_heroes_list'])

        return True

    def get_hero_scroll_position(self, menu_name, hero_name):

        return self.menus[menu_name]['sb_position'][hero_name]

    def set_hero_scroll_position(self, menu_name, hero_name):
        sbp = self.get_scroll_pos(menu_name)
        hsbp = self.get_hero_scroll_position(self, menu_name, hero_name)
        if hsbp is None:
            self.init_hero_scroll_position(menu_name, hero_name)

        self.menus[menu_name][hero_name]['sb_position']
        self.get_scroll_pos(menu_name)

    def scroll_to_hero(self, menu_name, hero_name):
        if hero_name is None:
            return None
        self.open_menu(menu_name)
        sorted_heroes_list = self.get_sorted_heroes_list(menu_name)
        if sorted_heroes_list is None:
            return None

        direction = None
        while True:
            visible_heroes = self.get_visible_heroes(menu_name)
            if not visible_heroes:
                return None
            pass
            hero_reg_dict = dict(visible_heroes)
            visible_heroes_names = list(zip(*visible_heroes))[0]
            top_vh = visible_heroes_names[0]
            bottom_vh = visible_heroes_names[-1]

            if direction == WHEEL_DOWN or direction is None:
                # Adding heroes in the end of of sorted_heroes_list
                lst = [name for name in visible_heroes_names if name not in sorted_heroes_list]
                sorted_heroes_list.extend(lst)

            next_hero_name_list = self.get_next_hero_name(menu_name, hero_name)
            if not next_hero_name_list:
                return None
            if set(next_hero_name_list).issubset(sorted_heroes_list) and hero_name != bottom_vh:
                next_hero_name = next_hero_name_list[0]
                # We need that next_hero_name is visible also as hero_name
                # So lvlup button is between them

                if sorted_heroes_list.index(next_hero_name) > sorted_heroes_list.index(bottom_vh):
                    direction = WHEEL_DOWN

                elif sorted_heroes_list.index(hero_name) < sorted_heroes_list.index(top_vh):
                    direction = WHEEL_UP

                if all(h in visible_heroes_names for h in (hero_name, next_hero_name)):
                    hero_name_reg = hero_reg_dict[hero_name]
                    next_hero_name_reg = hero_reg_dict[next_hero_name]
                    hero_reg_height = next_hero_name_reg.y - hero_name_reg.y
                    hero_reg = Region(0, hero_name_reg.y, hero_name_reg.getRight(), hero_reg_height)
                    break
            else:
                # May be we are at the end of heroes list
                # So we need that lvlup button is visible below hero name
                direction = WHEEL_DOWN
                if hero_name in visible_heroes_names:

                    # button_patterns = self.get_pattern('heroes_button', 'lvlup_')
                    bottom_patterns = self.get_pattern('heroes_button', 'edge_')
                    hero_name_reg = hero_reg_dict[hero_name]
                    hero_reg_height = self.window.getClientRegion().getHeight() - hero_name_reg.y
                    hero_reg = Region(0, hero_name_reg.y, hero_name_reg.getRight(), hero_reg_height)

                    # Check that we have lvlup button in butt_reg
                    if self.find_pattern_reg_name_single(hero_reg, bottom_patterns):
                        break

            # if direction == WHEEL_UP:
            #     # Adding heroes in front of sorted_heroes_list
            #     hol[0:0] = [item for item in visible_heroes_names if item not in hol]
            # elif direction == WHEEL_UP:
            #     # Adding heroes in the end of of sorted_heroes_list
            #     hol.extend([item for item in visible_heroes_names if item not in hol])

            if direction:
                if direction == WHEEL_DOWN:
                    self.scroll_menu(menu_name, WHEEL_UP)
                    self.scroll_menu(menu_name, WHEEL_DOWN)
                self.scroll_menu(menu_name, direction)

        img = self.window.getScreenshot(hero_reg).get_array()
        cv2.imshow('scroll_to_hero:hero_reg', img)
        cv2.waitKey(50)
        return hero_reg

    def get_lvlup_toggle(self):
        return 'z'

    def needToUpgrade(self):
        numberOfSkill = [len(v) for v in self.menus['mainMenu']['skills'].values()]

        if numberOfSkill == SKILL_NUMBER:
            return False
        return True

    def get_scroll_min_pos(self, menu_name):
        return self.menus[menu_name]['sb_min_position']

    def get_scroll_max_pos(self, menu_name):
        return self.menus[menu_name]['sb_max_position']

    def set_scroll_pos(self, menu_name, pos):
        self.menus[menu_name]['sb_position'] = pos

    def scroll_pos_inc(self, menu_name, count=1):
        self.set_scroll_pos(self, menu_name, self.get_scroll_pos(menu_name) + count)

    def scroll_menu(self, menu_name, direction, count=1):
        self.open_menu(menu_name)
        if not self.find_pattern_from_list(self.get_pattern('main', 'scroll_')):
            return None
        for i in range(count):
            # mouse_event = MouseScroll(self.window, direction)
            # self.mouse_event_queue.put((mouse_event, self.mp_event))
            # self.mp_event.wait()
            self.window.scroll(direction)
            self.menus[menu_name]['sb_position'] -= direction
        time.sleep(0.3)
        self.window.makeScreenshotClientAreaRegion()
        self.invalidate_cache_state()

    def scroll_to_position(self, menu_name, position):
        if position is None:
            return
        cur_pos = self.get_scroll_pos(menu_name)
        if position < cur_pos:
            direction = WHEEL_UP
        elif position > cur_pos:
            direction = WHEEL_DOWN
        else:
            return
        self.scroll_menu(menu_name, direction, abs(position - cur_pos))

    def scroll_to_start(self, menu_name):
        self.scroll_to_position(menu_name, self.get_scroll_min_pos(menu_name))

    def scroll_to_last(self, menu_name):
        self.scroll_to_position(menu_name, self.get_scroll_max_pos(menu_name))

    def findItem(self, item):
        if item['pattern']['location'] is None:
            self.window.getScreenshot('').find_pattern(item['pattern'])

    def nextLvl(self):
        self.open_menu('mainMenu')
        self.clickItem(self.findItem(self.menus['mainMenu']['nextLvlButton']))

    def prevLvl(self):
        self.open_menu('mainMenu')
        self.clickItem(self.findItem(self.menus['mainMenu']['prevLvlButton']))

    def upgradeTopHero(self, offset=0):
        self.open_menu('heroesTab')
        h = self.findTopHero()
        self.lvlUpHero(h)

    def get_current_menu(self):
        name = None
        for menu_name in ['news', 'ancients_summon', 'settings', 'shop', 'heroes', 'ancients', 'relics', 'clan',
                          'merceneries', 'transcendence']:
            # Check that 
            reg = self.find_pattern_from_list(self.get_pattern('main', menu_name + '_menu_active'))
            if reg:
                name = menu_name
                break
        return name

    def open_menu(self, menu_name):
        cur_menu = self.get_current_menu()
        if DEBUG:
            print('open_menu: menu name is %s ' % (cur_menu))
        if cur_menu == menu_name:
           return
        self.close_menu(wait=None)
        pat_list = self.get_pattern('main', menu_name + '_menu')
        reg = self.find_pattern_from_list(pat_list)
        if not reg:
            return None
        self.click_location(reg[0].center())

    def getCurrentMenu(self):
        return self.currentmenu_name

    def close_menu(self, menu_name=None,wait=1):
        # self.wait_for_pattern_name(menu_name, 'close_menu')
        while 1:
            self.wait_for_pattern_list(self.get_pattern('buttons', 'button_close_menu'),wait=wait)
            if not self.click_pattern('buttons', 'button_close_menu', all=True):
                break


        # self.click_pattern(menu_name, 'close_menu', all=False)

    def close_popups(self, menu_name):
        self.wait_for_pattern_name(menu_name, 'close_menu')
        self.click_pattern(menu_name, 'close_menu', all=False)

    def wait_for_pattern_name(self, menu_name, pat_name):
        pat_list = self.get_pattern(menu_name, pat_name)
        return self.wait_for_pattern_list(pat_list)

    def wait_for_pattern_list(self, pat_list, wait=1):
        delay = 0.05
        wait_start = time.clock()
        total_delay = 0

        while wait is None or wait==-1 or total_delay <= wait:
            self.window.makeScreenshotClientAreaRegion()
            reg=self.find_pattern_from_list(pat_list)
            if reg:
                return reg
            if wait is None:
                return None
            time.sleep(delay)
            # if time.clock() - wait_start >= wait:
            #     return None
            total_delay += delay
            delay *= 2
        return None

    def click_pattern(self, menu_name, pattern_name, all=False, refresh=True):
        if refresh:
            self.window.makeScreenshotClientAreaRegion()
        patt_list = self.get_pattern(menu_name, pattern_name)
        if patt_list:
            regs = self.find_pattern_from_list(patt_list,all=all)
            if regs:
                for reg in regs:
                    self.click_region(reg)
                    if not all:
                        break
                if refresh:
                    self.window.makeScreenshotClientAreaRegion()
                return True
        return None

    def get_monster_click_location(self):
        if not self.click_monster_location:
            next_lvl_button = self.find_pattern_from_list(self.get_pattern('main', 'levelnext'))
            if next_lvl_button:
                next_lvl_button = next_lvl_button[0]
            else:
                return None

            prev_lvl_button = self.find_pattern_from_list(self.get_pattern('main', 'levelprev'))
            if prev_lvl_button:
                prev_lvl_button = prev_lvl_button[0]
            else:
                return None
            skull_hp = self.find_pattern_from_list(self.get_pattern('main', 'skull_hp'))
            if skull_hp:
                skull_hp = skull_hp[0]
            else:
                return None
            x_n, y_n = next_lvl_button.center().get_xy()
            x_p, y_p = prev_lvl_button.center().get_xy()
            shop_y = skull_hp.center().get_y()
            # click_x is halfway between next and previous level button
            click_x = (x_p + x_n) // 2
            # click_y is halfway between current level rect and shop button
            click_y = (shop_y + y_n) // 2
            self.click_monster_location = Location(click_x, click_y)
        return self.click_monster_location

    # def get_monster_click_location(self):
    #     if self.click_monster_location is None:
    #         self.set_monster_click_location()

        return self.click_monster_location

    def click_monster(self, cps=10):
        mcl = self.get_monster_click_location()
        if not mcl:
            return None
        return self.click_location(mcl)

    def collect_fish(self, timer=15):

        curr_time = time.clock()
        if curr_time - self.fish_time >= timer:
            self.window.makeScreenshotClientAreaRegion()

            self.fish_time = curr_time
            return self.click_pattern('main', 'fish')

    def collect_newyear(self, timer=30):
        curr_time = time.clock()
        if curr_time - self.newyear >= timer:
            self.newyear = curr_time
            return self.click_pattern('main', 'new_year')
        return None

    def collect_relic_ooze(self):
        # if not self.relic_ooze_collected:
        self.window.makeScreenshotClientAreaRegion()
        if self.find_pattern_from_list(self.get_pattern('main', 'relic_ooze')):
            with self.lock:
                if self.click_location(self.window.getClientRegion().center(), refresh=True):
                    self.close_menu('relic_ooze')
                    self.relic_ooze_collected = True

    def lvlup(self):
        self.click_pattern('heroes_button', 'lvlup_active')

    def ascend(self, ascension_life=3600, check_timer=60, check_progress=True, check_hero_souls=True):
        self.window.makeScreenshotClientAreaRegion()
        self.click_location(Location(1, 1), refresh=True)

        curr_time = time.clock()
        if curr_time - self.ascend_checker_time < check_timer:
            return None
        self.ascend_checker_time = curr_time

        if curr_time - self.ascend_time < ascension_life:
            return None
        if self.got_heroes_souls == False and check_hero_souls:
            got_heroes_souls = self.find_pattern_from_list(self.get_pattern('main', 'got_heroes_souls'))
            if got_heroes_souls:
                self.got_heroes_souls = True
            else:
                return None

        progress_on = self.find_pattern_from_list(self.get_pattern('main', 'button_progression_on'))
        if progress_on and check_progress:
            return None
        # if not self.find_pattern_from_list(self.get_pattern('main', 'button_ascend')):
        #     if self.get_hero_level('heroes', 'amenhotep') < 200:
        #         if not self.lvlup_hero('heroes', 'amenhotep', max_level=200):
        #             return None
        cnt = 0
        while not self.wait_for_pattern_list(self.get_pattern('main', 'button_ascend'), wait=1) and cnt < 10:
            self.lvlup_hero('heroes', 'amenhotep', lvl_count=100)
            cnt += 1

        destroy_relics_pat = self.get_pattern('main', 'destroy_relics')
        wish_to_ascend_pat = self.get_pattern('main', 'wish_to_ascend')
        # Refresh screenshot
        self.window.makeScreenshotClientAreaRegion()
        # if self.find_pattern_from_list(self.get_pattern('main', 'button_ascend')):
        if self.wait_for_pattern_list(self.get_pattern('main', 'button_ascend')):
            with self.lock:
                if self.click_pattern('main', 'button_ascend'):
                    if self.wait_for_pattern_list(destroy_relics_pat):
                        self.click_pattern('main', 'button_yes')
                    if self.wait_for_pattern_list(wish_to_ascend_pat):
                        if self.click_pattern('main', 'button_yes'):
                            time.sleep(5)
                            curr_time = time.clock()
                            self.menus['heroes']['last_available_hero'] = None
                            self.menus['heroes']['max_seen_hero'] = None
                            self.menus['heroes']['visible_heroes_cache'] = None
                            self.menus['heroes']['hero_level'] = {}
                            # self.save_heroes_levels('heroes', self.get_heroes_level_dict('heroes'))
                            self.save_container('heroes', 'hero_level', self.menus['heroes']['hero_level'])
                            self.starter_clicks = True
                            self.got_heroes_souls = False
                            self.ascend_time = curr_time
                            self.lvlup_all_heroes_time = curr_time
                            self.click_pattern('main', 'button_progression_off')
                            self.buy_quick_ascension()

    def monster_clicker(self, count=100, cps=30):
        for i in range(count):
            if not self.click_monster(cps):
                break

    def collect_gilds(self):
        self.window.makeScreenshotClientAreaRegion()
        present_reg = self.find_pattern_from_list(self.get_pattern('main', 'transcension_highest_zone_gift'))
        if present_reg:
            with self.lock:
                if self.click_pattern('main', 'transcension_highest_zone_gift'):
                    transcension_highest_zone_menu = self.get_pattern('main', 'transcension_highest_zone_menu')
                    if self.wait_for_pattern_list(transcension_highest_zone_menu):
                        if self.click_location(self.window.getClientRegion().center(), refresh=True):
                            self.close_menu('main')

    def get_np_level(self):
        next_lvl_button = self.find_pattern_from_list(self.get_pattern('main', 'levelnext'))
        if next_lvl_button:
            next_lvl_button = next_lvl_button[0]
        else:
            return None
        prev_lvl_button = self.find_pattern_from_list(self.get_pattern('main', 'levelprev'))
        if prev_lvl_button:
            prev_lvl_button = prev_lvl_button[0]
        else:
            return None

        x_n, y_n = next_lvl_button.center().get_xy()
        x_p, y_p = prev_lvl_button.center().get_xy()
        x_curr_level, y_curr_level = ((x_n + x_p) / 2, (y_n + y_p) / 2)
        x_next_level = x_curr_level + 0.4 * (x_n - x_curr_level)
        y_next_level = y_curr_level
        x_prev_level = x_curr_level - 0.4 * (x_curr_level - x_p)
        y_prev_level = y_curr_level
        return (Location(x_prev_level, y_prev_level), Location(x_next_level, y_next_level))

    def next_level(self):
        skull_farm = self.find_pattern_from_list(self.get_pattern('main', 'skull_farm'))
        if skull_farm:
            return

        np_level = self.get_np_level()
        if np_level:
            next_level = self.get_np_level()[1]
        else:
            return None
        if next_level:
            self.click_location(next_level)

    def prev_level(self):

        np_level = self.get_np_level()
        if np_level:
            prev_level = np_level[0]
        else:
            return None
        self.click_location(prev_level)

    def progress_auto(self, farm_mode_timer=300, boss_timer=5):
        curr_time = time.clock()
        progress_off = self.find_pattern_from_list(self.get_pattern('main', 'button_progression_off'))
        progress_on = self.find_pattern_from_list(self.get_pattern('main', 'button_progression_on'))

        if progress_on and self.stuck_on_boss(boss_time=boss_timer, check_interval=1):
            self.prev_level()
            self.farm_mode_start_time = curr_time
            self.click_pattern('main', 'button_progression_off')
            return True

        if not progress_off:
            return False

        if progress_off and self.farm_mode_start_time is None:
            self.farm_mode_start_time = curr_time
            return True

        if curr_time - self.farm_mode_start_time >= farm_mode_timer:
            self.farm_mode_start_time = None
            self.click_pattern('main', 'button_progression_off')
            return True

    def stuck_on_boss(self, boss_time, check_interval=5):
        curr_time = time.clock()

        if self.boss_time and curr_time - self.boss_check_time <= check_interval:
            return False
        self.boss_check_time = curr_time
        boss_clock = self.find_pattern_from_list(self.get_pattern('main', 'boss_clock'))
        if not boss_clock:
            return False
        skull_farm = self.find_pattern_from_list(self.get_pattern('main', 'skull_farm'))
        if not skull_farm:
            return False

        if not self.levels_region:
            next_lvl_button = self.find_pattern_from_list(self.get_pattern('main', 'levelnext'))[0]
            prev_lvl_button = self.find_pattern_from_list(self.get_pattern('main', 'levelprev'))[0]
            x_n, y_n = next_lvl_button.getBottomRight().get_xy()
            x_p, y_p = prev_lvl_button.getTopLeft().get_xy()
            x_c, y_c = (x_n + x_p) / 2, (y_n + y_p) / 2
            h = (y_c - y_p) * 2
            y_p = int(y_c - h)
            y_n = int(y_c + h)
            self.levels_region = Region.from2POINT(x_p, y_p, x_n, y_n)
        time.sleep(1.1)
        if self.boss_time is None:
            self.boss_time = curr_time
            self.levels_region_scrshot = self.window.makeScreenshotClientAreaRegion(self.levels_region)
            # cv2.imshow('self.levels_region_scrshot', self.levels_region_scrshot.get_array())
            # cv2.waitKey(50)
            return False
        self.boss_check_time = curr_time
        if curr_time - self.boss_time >= boss_time:
            levels_region_scrshot = self.window.makeScreenshotClientAreaRegion(self.levels_region)
            levels_region_scrshot.set_name('123456')
            # cv2.imshow('levels_region_scrshot',levels_region_scrshot.get_array())
            # cv2.imshow('self.levels_region_scrshot', self.levels_region_scrshot.get_array())
            # cv2.waitKey(50)
            self.boss_time = None
            if levels_region_scrshot.find_pattern(self.levels_region_scrshot):
                # cv2.imshow('levels_region_scrshot',levels_region_scrshot.get_array())
                # cv2.imshow('self.levels_region_scrshot', self.levels_region_scrshot.get_array())
                # cv2.waitKey(50)
                return True
        return False

    def progress_manual(self, farm_mode_timer=300, boss_timer=10):
        curr_time = time.clock()
        if self.farm_mode_start_time and curr_time - self.farm_mode_start_time > farm_mode_timer:
            self.farm_mode_start_time = None
            # return False
        if not self.farm_mode_start_time:
            self.next_level()

        if not self.farm_mode_start_time and self.stuck_on_boss(boss_time=boss_timer, check_interval=1):
            self.prev_level()
            self.farm_mode_start_time = curr_time
            return True
        return False

    def progress_level(self, farm_mode_timer=300, boss_timer=30, progress_button_timer=30):
        self.window.makeScreenshotClientAreaRegion()

        curr_time = time.clock()
        progress_button = None
        if self.progress_button_time and curr_time - self.progress_button_time >= progress_button_timer:
            progress_button = self.find_pattern_from_list(self.get_pattern('main', 'button_progression'))
            if progress_button:
                self.progress_button_time = None
            else:
                self.progress_button_time = curr_time
        if progress_button or self.progress_button_time is None:
            return self.progress_auto(farm_mode_timer=farm_mode_timer, boss_timer=boss_timer)
        return self.progress_manual(farm_mode_timer=farm_mode_timer, boss_timer=boss_timer)

    def get_cache_state(self):
        return self.cache_state

    def invalidate_cache_state(self):
        self.cache_state = False

    def validate_cache_state(self):
        self.cache_state = True

    def cache_state_is_invalid(self):
        return not self.get_cache_state()

    def cache_state_is_valid(self):
        return self.get_cache_state()

    # def buy_available_upgrades_old(self):
    #     self.window.makeScreenshotClientAreaRegion()
    #
    #     menu_name = 'heroes'
    #     max_seen_hero = self.get_max_seen_hero(menu_name)
    #     if max_seen_hero is None:
    #         return None
    #     self.scroll_to_hero(menu_name, max_seen_hero)
    #     while not self.click_pattern('main', 'buy_available_upgrades_old'):
    #         self.scroll_menu(menu_name, WHEEL_DOWN)
    #         self.scroll_menu(menu_name, WHEEL_UP)
    #         self.scroll_menu(menu_name, WHEEL_DOWN)

    def buy_available_upgrades(self, upgrades_timer=300):
        curr_time = time.clock()
        if curr_time - self.skills_upgrades_time < upgrades_timer:
            return None

        self.window.makeScreenshotClientAreaRegion()
        menu_name = 'heroes'
        max_seen_hero = self.get_max_seen_hero(menu_name)
        last_ascend_seen_heroes=self.get_last_ascend_seen_heroes(menu_name)
        if max_seen_hero is None:
            return None
        self.scroll_to_hero(menu_name, max_seen_hero)
        cnt = 0
        MAX_RETRY = 3
        while cnt <= MAX_RETRY:
            if not self.click_pattern('main', 'buy_available_upgrades'):
                self.scroll_menu(menu_name, WHEEL_DOWN)
                self.scroll_menu(menu_name, WHEEL_UP)
                self.scroll_menu(menu_name, WHEEL_DOWN)
            else:
                self.skills_upgrades_time = time.clock()
                return True
            cnt += 1

        self.window.makeScreenshotClientAreaRegion()



        sorted_hero_list = self.get_sorted_heroes_list(menu_name)
        if sorted_hero_list is None:
            return None
        heroes_upgraded_list = self.menus[menu_name]['heroes_upgraded_list']
        # if heroes_upgraded_list is None:
        #     return None


        # heroes_to_lvlup = [hero_name for hero_name in last_ascend_seen_heroes if hero_name not in heroes_upgraded_list]
        #Make list from sorted heroes list up to max_seen_hero included.
        heroes_to_lvlup = list(itertools.takewhile(lambda x: x != max_seen_hero, sorted_hero_list))+[max_seen_hero]
        #Exclude from this list upgraded heroes
        heroes_to_lvlup = [hero_name for hero_name in heroes_to_lvlup if hero_name not in heroes_upgraded_list]

        for hero_name in heroes_to_lvlup:
            ###Buy heroes skill except ascension
            hero_reg = self.scroll_to_hero(menu_name, hero_name)
            hero_reg_scr = self.window.makeScreenshotClientAreaRegion(hero_reg)

            ascend_skill_reg = None
            if hero_name == 'amenhotep':
                ascend_skill_reg = hero_reg_scr.find_pattern_from_list(
                    self.get_pattern('heroes_skills', 'amenhotep_ascend'),
                    cache=False)
                if ascend_skill_reg:
                    ascend_skill_reg = ascend_skill_reg[0]


            button_edge_reg = hero_reg_scr.find_pattern_from_list(self.get_pattern('heroes_button', 'edge_'),
                                                                  cache=False)
            if button_edge_reg is None:
                continue
            button_edge_reg = button_edge_reg[0]
            hero_name_reg = hero_reg_scr.find_pattern_from_list(self.get_pattern(menu_name, hero_name))
            if hero_name_reg is None:
                continue
            hero_name_reg = hero_name_reg[0]
            # skills_reg_left_x, skills_reg_left_y = button_edge_reg.center().get_xy()
            skills_reg_left_x, skills_reg_left_y = button_edge_reg.getRight(),button_edge_reg.center().get_y()
            skills_reg_right_x = hero_name_reg.getRight()
            y = hero_reg.getTop() + skills_reg_left_y
            for i in range(100):
                x = hero_reg.getLeft() + skills_reg_left_x + int(
                    random.random() * (skills_reg_right_x - skills_reg_left_x))
                if ascend_skill_reg and ascend_skill_reg.contains((x - hero_reg.getLeft(), y - hero_reg.getTop())):
                    continue
                # hero_reg_scr = self.window.makeScreenshotClientAreaRegion(hero_reg)
                # cv2.imshow("hero_reg_scr", hero_reg_scr.get_array())
                # cv2.waitKey(10)
                # skills_reg = hero_reg_scr.find_pattern_from_list(self.get_pattern('heroes_skills', '%s_c' % hero_name))
                # if skills_reg:
                #     break
                self.window.click(x, y, cps=30)
            hero_reg_scr = self.window.makeScreenshotClientAreaRegion(hero_reg)
            skills_reg = hero_reg_scr.find_pattern_from_list(self.get_pattern('heroes_skills', '%s_c' % hero_name))

            if skills_reg:
                # heroes_upgraded_list.remove(hero_name)
                heroes_upgraded_list = self.menus[menu_name]['heroes_upgraded_list']
                heroes_upgraded_list.append(hero_name)
                self.save_container(menu_name,'heroes_upgraded_list',heroes_upgraded_list)
            self.skills_upgrades_time = time.clock()
        return True

    def buy_quick_ascension(self):
        self.window.makeScreenshotClientAreaRegion()
        self.close_menu()
        with self.window.lock:
            if self.click_pattern('main', 'button_shop'):
                if self.wait_for_pattern_list(self.get_pattern('shop', 'shop_title')):
                    self.click_pattern('shop', 'button_buy_quick_ascension')
                    if self.wait_for_pattern_list(self.get_pattern('shop', 'buy_confirm')):
                        self.click_pattern('shop', 'button_yes')
                        if self.wait_for_pattern_list(self.get_pattern('shop', 'title_thank_you')):
                            #Close all shop submenu
                            self.click_pattern('shop', 'button_close_menu', all=True)
                            # self.click_pattern('shop', 'button_okey')
                            # if self.wait_for_pattern_list(self.get_pattern('shop', 'shop_title')):

                    else:
                        if self.wait_for_pattern_list(self.get_pattern('shop', 'title_you_need_more_rubies')):
                            self.click_pattern('shop', 'button_close_menu', all=True)
                            # self.click_pattern('shop', 'button_no')
                            return False
        return True

        menu_name = 'heroes'
        max_seen_hero = self.get_max_seen_hero(menu_name)
        if max_seen_hero is None:
            return None
        self.scroll_to_hero(menu_name, max_seen_hero)
        while not self.click_pattern('main', 'buy_available_upgrades'):
            self.scroll_menu(menu_name, WHEEL_DOWN)
            self.scroll_menu(menu_name, WHEEL_UP)
            self.scroll_menu(menu_name, WHEEL_DOWN)

    def try_skill_combos(self, *args):

        def is_skill_combo_available(skill_combo):
            for sn in skill_combo:
                if not self.find_pattern_from_list(self.get_pattern('skills', 'skill_%s' % sn)):
                    if DEBUG:
                        print("try_skill_combos: skill %s is not ready yet. Try another combo" % sn)
                    return False
            return True

        self.window.makeScreenshotClientAreaRegion()
        for combo in args:
            if is_skill_combo_available(combo):
                if DEBUG:
                    print("try_skill_combos: Combo %s is ready to activate" % combo)
                self.window.pressKeyList(combo)

    def start_play(self):
        if self.click_pattern('buttons','button_play'):
            if self.click_pattern('buttons', 'button_close_menu',all=True):
                return True
        return None

class Window:
    def __init__(self, hwnd, lock):
        self.hwnd = hwnd
        self.lock = lock
        self.screenshot = None
        self.last_click_location = (None, None)
        if DEBUG:
            print("Window:_init_:hwnd=%s" % (hwnd))
        winLong = GetWindowLong(self.hwnd, GWL_STYLE)
        # SetWindowLong(hwnd, GWL_STYLE, winLong & ~WS_SIZEBOX)

        # # SetWindowLong(self.hwnd, GWL_STYLE, winLong |WS_SYSMENU|WS_CAPTION| WS_MAXIMIZEBOX | WS_MINIMIZEBOX)
        # SetWindowLong(self.hwnd, GWL_STYLE, winLong |WS_SYSMENU|WS_CAPTION|  ~WS_MAXIMIZEBOX | ~WS_MINIMIZEBOX)
        pass

    def move(self, x, y):
        reg = self.getWindowRegion()
        SetWindowPos(self.hwnd,
                     HWND_TOP,
                     x,
                     y,
                     reg.w,
                     reg.h,
                     0)

    def resize(self, width, height):
        reg = self.getWindowRegion()
        SetWindowPos(self.hwnd,
                     HWND_TOP,
                     reg.x,
                     reg.y,
                     width,
                     height,
                     0)

    def resizeRel(self, dwidth, dheight):
        reg = self.getWindowRegion()
        SetWindowPos(self.hwnd,
                     HWND_TOP,
                     reg.x,
                     reg.y,
                     reg.w + dwidth,
                     reg.h + dheight,
                     0)

    def resizeCliPropW(self, width):
        self.resizeClientArea(width, int(width * 9.0 / 16))

    def resizeCliPropH(self, height):
        self.resizeClientArea(int(round(height * 16.0 / 9)), height)

    def resizeClientArea(self, width, height):
        cliReg = self.getClientRegion()
        dx = width - cliReg.getWidth()
        dy = height - cliReg.getHeight()
        self.resizeRel(dx, dy)

    def getClientRegion(self):
        cliRect = RECT()
        GetClientRect(self.hwnd, ctypes.byref(cliRect))
        return Region(cliRect.left, cliRect.top, cliRect.right - cliRect.left, cliRect.bottom - cliRect.top)

    def getWidth(self):
        return self.getClientRegion().getWidth()

    def getHeight(self):
        return self.getClientRegion().getHeight()

    def get_size(self):
        return self.getClientRegion().get_size()

    def getHeight(self):
        return self.getClientRegion().getHeight()

    def getWindowRegion(self):
        winRect = RECT()
        GetWindowRect(self.hwnd, ctypes.byref(winRect))
        return Region(winRect.left, winRect.top, winRect.right - winRect.left, winRect.bottom - winRect.top)

    def getRegionScreenShot(Region):
        return Image

    def pressKey(self, char):
        with self.lock:
            SendMessage(self.hwnd, WM_KEYDOWN, charToKeyCode(char), 1)
            # time.sleep(0.1)
            SendMessage(self.hwnd, WM_KEYUP, charToKeyCode(char), 1)

    def pressAndHoldKey(self, char):
        with self.lock:
            SendMessage(self.hwnd, WM_KEYDOWN, charToKeyCode(char), 1)

    def releaseKey(self, char):
        with self.lock:
            SendMessage(self.hwnd, WM_KEYUP, charToKeyCode(char), 1)

    def pressKeyList(self, chars):
        with self.lock:
            for c in chars:
                self.pressKey(c)
        return

    def getScreenshot(self, region=None):
        if region:
            return self.screenshot.crop(region)
        return self.screenshot

    def getScreenshotCliRegion(self, name):
        return self.getClientRegion().getScreenshot()

    def makeScreenshotClientAreaRegion(self, region=None):
        with self.lock:
            isIconic = IsIconic(self.hwnd)
            winLong = None
            # ShowWindow(self.hwnd, SW_HIDE)

            if isIconic:
                animationInfo = ANIMATIONINFO()
                animationInfo.iMinAnimate = 0
                animationInfo.cbSize = ctypes.sizeof(ANIMATIONINFO)

                winLong = GetWindowLong(self.hwnd, GWL_EXSTYLE)
                SetWindowLong(self.hwnd, GWL_EXSTYLE, winLong | WS_EX_LAYERED)
                SetLayeredWindowAttributes(self.hwnd, 0, 0, LWA_ALPHA)
                # SystemParametersInfo(SPI_GETANIMATION, animationInfo.cbSize,ctypes.byref(animationInfo), 0)

                SystemParametersInfo(SPI_SETANIMATION, animationInfo.cbSize, ctypes.byref(animationInfo),
                                     SPIF_SENDCHANGE)
                ShowWindow(self.hwnd, SW_SHOWNOACTIVATE)

            wr = RECT()
            cliRect = RECT()

            GetClientRect(self.hwnd, ctypes.byref(cliRect))
            if region is None:
                x = 0
                y = 0
                w = cliRect.right
                h = cliRect.bottom
            else:
                ir = region.intersection(Region.fromRECT(cliRect))
                if ir is None:
                    raise Exception(
                        'Region ' + str(region) + ' is not intersect with client area rectangle' + str(cliRect))

                x = ir.x
                y = ir.y
                w = ir.w
                h = ir.h

            # w = cliRect.right
            # h = cliRect.bottom
            # x = region.get_x()
            # y = region.get_y()
            # w = region.getWidth()
            # h = region.getHeight()


            hDC = GetDC(self.hwnd)
            myDC = CreateCompatibleDC(hDC)
            myBitMap = CreateCompatibleBitmap(hDC, w, h)
            SelectObject(myDC, myBitMap)
            BitBlt(myDC, 0, 0, w, h, hDC, x, y, SRCCOPY)
            if isIconic:
                ShowWindow(self.hwnd, SW_SHOWMINNOACTIVE)
                SetWindowLong(self.hwnd, GWL_EXSTYLE, winLong)
                # SystemParametersInfo(SPI_GETANIMATION, animationInfo.cbSize,ctypes.byref(animationInfo), 0)
                animationInfo = ANIMATIONINFO()
                animationInfo.iMinAnimate = 1
                animationInfo.cbSize = ctypes.sizeof(ANIMATIONINFO)
                SystemParametersInfo(SPI_SETANIMATION, animationInfo.cbSize, ctypes.byref(animationInfo),
                                     SPIF_SENDCHANGE)

            bmpScreen = BITMAP()
            GetObject(myBitMap, ctypes.sizeof(BITMAP), ctypes.byref(bmpScreen))
            bi = BITMAPINFOHEADER()
            bi.biSize = ctypes.sizeof(BITMAPINFOHEADER)
            bi.biWidth = bmpScreen.bmWidth
            bi.biHeight = bmpScreen.bmHeight
            bi.biPlanes = 1
            bi.biBitCount = bmpScreen.bmBitsPixel
            bi.biCompression = BI_RGB
            bi.biSizeImage = 0
            bi.biXPelsPerMeter = 0
            bi.biYPelsPerMeter = 0
            bi.biClrUsed = 0
            bi.biClrImportant = 0

            img = np.empty((h, w, int(bmpScreen.bmBitsPixel / 8)), np.uint8)
            winplace = WINDOWPLACEMENT()
            GetWindowPlacement(self.hwnd, ctypes.byref(winplace))
            wr = winplace.rcNormalPosition
            if (GetDIBits(hDC, myBitMap, 0,
                          bmpScreen.bmHeight,
                          ctypes.c_void_p(img.ctypes.data),
                          ctypes.byref(bi), DIB_RGB_COLORS) == 0):
                return None
        DeleteDC(myDC)
        DeleteObject(myBitMap)
        ReleaseDC(self.hwnd, hDC)
        screenshot = Image.fromArray(cv2.flip(img, 0))
        screenshot.set_name('Screenshot of %s %s' % (self.hwnd, id(screenshot)))
        if region is None:
            self.screenshot = screenshot
        return screenshot

    def scroll(self, direction, x=1, y=1):
        with self.lock:
            tmp = (y << 16) | x
            SendMessage(self.hwnd, WM_MOUSEWHEEL,
                        (WHEEL_DELTA * direction) << 16, tmp)
            time.sleep(0.02)
            x = 1
            y = 1
            tmp = (y << 16) | x
            SendMessage(self.hwnd, WM_MOUSEMOVE, 0, tmp)

    def scrollDown(self):
        self.scrollDown(1, 1)

    def scrollUp(self):
        self.scrollUp(1, 1)

    def scrollDown(self, x, y):
        tmp = (y << 16) | x
        SendMessage(self.hwnd, WM_MOUSEWHEEL,
                    (WHEEL_DELTA * -1) << 16, tmp)

    def scrollUp(self, x, y):
        tmp = (y << 16) | x
        SendMessage(self.hwnd, WM_MOUSEWHEEL,
                    (WHEEL_DELTA * 1) << 16, tmp)

    def click(self, x, y, refresh=False, park=True, cps=30):

        x = int(x)
        y = int(y)
        self.last_click_location = (x, y)
        tmp = (y << 16) | x
        delay = 1 / cps
        # if park:
        #     delay /= 2

        err = 0
        with self.lock:
            err += SendMessage(self.hwnd, WM_LBUTTONDOWN, 0, tmp)
            err += SendMessage(self.hwnd, WM_LBUTTONUP, 0, tmp)
            time.sleep(delay)
            if park:
                x = 1
                y = 1
                tmp = (y << 16) | x
                err += SendMessage(self.hwnd, WM_MOUSEMOVE, 0, tmp)
                # time.sleep(delay / 2)

        if refresh:
            self.makeScreenshotClientAreaRegion()
        if err > 0:
            return None
        return True

    def move_mouse(self, x=None, y=None, refresh=False, park=True, cps=30):
        l_x, l_y = self.last_click_location
        xc, yc = l_x, l_y
        steps = 30
        if x:
            dx = (x - l_x) / steps
        else:
            dx = 0
        if y:
            dy = (y - l_y) / steps
        else:
            dy = 0

        for i in range(steps):
            xc += dx
            yc += dy
            xi, yi = int(xc), int(yc)
            tmp = (yi << 16) | xi
            delay = 1 / cps
            err = 0
            with self.lock:
                err += SendMessage(self.hwnd, WM_MOUSEMOVE, 0, tmp)
                time.sleep(delay)
        if err > 0:
            return None
        return True

    def click_location(self, loc, refresh=False, park=True, cps=50):
        return self.click(loc.get_x(), loc.get_y(), refresh=refresh, park=park, cps=cps)

    def click_region(self, reg, refresh=False, park=True, cps=30):
        x, y = reg.center().get_xy()
        return self.click(x, y, refresh=refresh, park=park, cps=cps)


class Location:
    def __init__(self, x, y):
        self.x = x
        self.y = y

    def get_x(self):
        return self.x

    def get_y(self):
        return self.y

    def set(self, x, y):
        self.x = x
        self.y = y

    def get_xy(self):
        return (self.x, self.y)


class Region:
    def __init__(self, x, y, w, h):
        self.x = x
        self.y = y
        self.w = w
        self.h = h

    # def get_xy(self):
    #     self.hwnd = hwnd
    #     r = RECT()
    #     GetWindowRect(hwnd, ctypes.byref(r))
    #     (self.x, self.y, self.w, self.h) = (r.left, r.top, r.right - r.left, r.bottom - r.top)
    @classmethod
    def fromRECT(cls, rect):
        return cls(rect.left, rect.top, rect.right - rect.left, rect.bottom - rect.top)

    @classmethod
    def from2POINT(cls, left, top, right, bottom):
        return cls(left, top, right - left, bottom - top)

    @classmethod
    def from2Location(cls, l1, l2):
        x1, y1 = l1.get_xy()
        x2, y2 = l2.get_xy()
        w = x2 - x1
        h = y2 - y1
        return cls(x1, y1, w, h)

    def getTopLeft(self):
        return Location(self.getLeft(), self.getTop())

    def getTopRight(self):
        return Location(self.getRight(), self.getTop())

    # def __eq__(self, other):
    #     if isinstance(other, Region):
    #         return self.is_intersect(other)
    #     return NotImplemented
    #
    # def __hash__(self):
    #     # return hash((self.x,self.y,self.w,self.h))
    #     return 1

    @property
    def getBottomLeft(self):
        return Location(self.getLeft(), self.getbottom())

    def getBottomRight(self):
        return Location(self.getRight(), self.getBottom())

    def resize(self, x, y, w, h):
        return 1

    def getX(self):
        return self.x

    def getY(self):
        return self.y

    def getWidth(self):
        return self.w

    def getHeight(self):
        return self.h

    def get_size(self):
        return self.w, self.h

    def getLeft(self):
        return self.x

    def getRight(self):
        return self.x + self.w

    def getTop(self):
        return self.y

    def getBottom(self):
        return self.y + self.h

    def setLeft(self, left):
        self.x = left

    def setRight(self, right):
        self.w = right - self.x

    def setTop(self, top):
        self.y = top

    def setBottom(self, bottom):
        self.h = bottom - self.y

    def center(self):
        return Location(int(self.x + self.w / 2), int(self.y + self.h / 2))

    ###################################
    #
    #      t1
    #   |----------------|
    # l1|                |r1
    #   |                |
    #   |          maxt  |  t2
    #   |        |-------|------|
    #   |    maxl|#######|minr  |
    #   |--------|-------|      |
    #      b1    | minb         |
    #            |              |
    #          l2|              |r2
    #            |              |
    #            |--------------|
    #                       b2
    #
    ###################################
    def intersection(self, region):
        t1 = self.getTop()
        b1 = self.getBottom()
        l1 = self.getLeft()
        r1 = self.getRight()
        t2 = region.getTop()
        b2 = region.getBottom()
        l2 = region.getLeft()
        r2 = region.getRight()
        maxt = max(t1, t2)
        minb = min(b1, b2)
        maxl = max(l1, l2)
        minr = min(r1, r2)

        if not (maxt < minb and maxl < minr):
            return None
        return Region(maxl, maxt, minr - maxl, minb - maxt)

    def is_intersect(self, region):
        t1 = self.getTop()
        b1 = self.getBottom()
        l1 = self.getLeft()
        r1 = self.getRight()
        t2 = region.getTop()
        b2 = region.getBottom()
        l2 = region.getLeft()
        r2 = region.getRight()
        maxt = max(t1, t2)
        minb = min(b1, b2)
        maxl = max(l1, l2)
        minr = min(r1, r2)

        if (maxt > minb or maxl > minr):
            return False
        return True

    def contains(self, loc):
        return self.getLeft() <= loc[0] <= self.getRight() and self.getTop() <= loc[1] <= self.getBottom()

    def __add__(self, x):
        return Region(self.getX() + x[0], self.getY() + x[1], self.getWidth(), self.getHeight())


def get_collectables(click_lock, start_barrier):
    ch = ClickerHeroes(click_lock)
    print("get_collectables: Started")
    ch.start_play()
    start_barrier.wait()
    while True:
        # try:
        ch.collect_fish()
        ch.collect_gilds()
        if ch.collect_newyear():
            ch.monster_clicker(count=750)
        ch.collect_relic_ooze()
        ch.monster_clicker()
        # except Exception as e:
        #     print("get_collectables:Exception:%s" % repr(e))
        #     continue


def levelup_heroes(click_lock,start_barrier):
    start_barrier.wait()
    print("levelup_heroes: Started")
    ch = ClickerHeroes(click_lock)
    while True:
        # try:
        # ch.window.makeScreenshotClientAreaRegion()
        # ch.buy_quick_ascension()
        ch.reindex_heroes_list('heroes')
        #     if ch.lvlup_all_heroes('heroes', max_level=150, timer=600):
        #         continue
        ch.lvlup_top_heroes('heroes')
        # ch.buy_quick_ascension()

        ch.lvlup_all_heroes('heroes', timer=60)
        ch.buy_available_upgrades(upgrades_timer=30)
        ch.ascend(ascension_life=60, check_timer=30, check_progress=False)
        # except Exception as e:
        #     print("levelup_heroes:Exception:%s" % repr(e))
        #     continue


def progress_levels(click_lock,start_barrier):
    start_barrier.wait()
    print("progress_levels: Started")
    ch = ClickerHeroes(click_lock)
    while True:
        # try:
        # img = ch.window.getScreenshot().get_canny_array()
        # cv2.imshow('Clicker Heroes', img)

        ch.progress_level(farm_mode_timer=300, boss_timer=30)
        # ch.try_skill_combos('12345')
        ch.try_skill_combos('869', '123457')
        # except Exception as e:
        #     print("progress_levels:Exception:%s" % repr(e))
        #     continue



if __name__ == '__main__':
    c_lock = multiprocessing.RLock()
    start_condition = multiprocessing.Condition()
    mp_target = [progress_levels, get_collectables, levelup_heroes]
    # mp_target = [levelup_heroes]
    start_barrier=multiprocessing.Barrier(len(mp_target))
    proc = []
    for target in mp_target:
        proc.append(Process(target=target, args=(c_lock,start_barrier,)))
    for p in proc:
        p.start()

    ch = ClickerHeroes(c_lock)

    while True:
        time.sleep(1)
        if DEBUG:
            print("Bot is running")
