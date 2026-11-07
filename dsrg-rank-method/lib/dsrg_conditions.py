
import json
import re
import sys
from fractions import Fraction
from math import isqrt


def complement(params):
    v, k, t, lam, mu = params
    return (v, v - k - 1, v - 2 * k + t - 1, v - 2 * k + mu - 2, v - 2 * k + lam)


