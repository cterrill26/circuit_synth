import hwtypes as ht
import pytest
import random
from src.node import Add, Equals, Mux

@pytest.mark.parametrize(
    "N,x,y", 
    [(8, random.randint(0, 255), random.randint(0, 255)) for _ in range(10)])
def test_add(N, x, y):
    x_ = ht.SMTBitVector[N](x)
    y_ = ht.SMTBitVector[N](y)
    adder = Add(N = N)
    res = adder(x_,y_)
    assert res[0].value.constant_value() == ((x + y) % 2**N)

@pytest.mark.parametrize(
    "N,x,y", 
    [(4, 8, 8), (2, 0, 1), (15, 96, 96), (27, 100, 1)])
def test_equal(N, x, y):
    x_ = ht.SMTBitVector[N](x)
    y_ = ht.SMTBitVector[N](y)
    equals = Equals(N = N)
    res = equals(x_,y_)
    assert res[0].value.constant_value() == (x == y)

@pytest.mark.parametrize(
    "N,s,x,y", 
    [(4, 1, 7, 8), (2, 0, 1, 0), (15, 1, 0, 96), (27, 0, 100, 1)])
def test_mux(N, s, x, y):
    s_ = ht.SMTBit(s)
    x_ = ht.SMTBitVector[N](x)
    y_ = ht.SMTBitVector[N](y)
    mux = Mux(N = N)
    res = mux(s_, x_,y_)
    assert res[0].value.constant_value() == (x if s else y)