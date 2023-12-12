import pono
import pytest
import random
import smt_switch as ss
import smt_switch.primops as ops
from smt_switch.sortkinds import BOOL, BV
from src.nodes import Nodes

solver = ss.create_btor_solver(False)
solver.set_opt('incremental', 'true')
fts = pono.FunctionalTransitionSystem(solver)
ur = pono.Unroller(fts)
nodes = Nodes(fts, 16)

@pytest.mark.parametrize(
    "N,x,y", 
    [(8, random.randint(0, 255), random.randint(0, 255)) for _ in range(10)])
def test_add(N, x, y):
    BVN = solver.make_sort(BV, N)
    x_ = solver.make_term(x, BVN)
    y_ = solver.make_term(y, BVN)
    adder = nodes.Add(N = N, delay = 0)
    res = adder(x_, y_)
    assert res[0] == solver.make_term(((x + y) % 2**N), BVN)

@pytest.mark.parametrize(
    "x,y,delay", 
    [(4, 1, 7), (2, 0, 1), (15, 1, 0), (27, 0, 100)])
def test_add_delay(x, y, delay):
    BVsort = solver.make_sort(BV, 16)
    x_ = solver.make_term(x, BVsort)
    y_ = solver.make_term(y, BVsort)
    add = nodes.Add(N = 4, delay = delay)
    res = add.timing(x_,y_)
    assert res[0] == solver.make_term(max(x, y) + delay, BVsort)

@pytest.mark.parametrize(
    "N,x,y", 
    [(4, 8, 8), (2, 0, 1), (15, 96, 96), (27, 100, 1)])
def test_equal(N, x, y):
    BVN = solver.make_sort(BV, N)
    x_ = solver.make_term(x, BVN)
    y_ = solver.make_term(y, BVN)
    equal = nodes.Equal(N = N, delay = 0)
    res = equal(x_, y_)
    assert res[0] == solver.make_term(int(x == y), solver.make_sort(BOOL))

@pytest.mark.parametrize(
    "x,y,delay", 
    [(4, 1, 7), (2, 0, 1), (15, 1, 0), (27, 0, 100)])
def test_equal_delay(x, y, delay):
    BVsort = solver.make_sort(BV, 16)
    x_ = solver.make_term(x, BVsort)
    y_ = solver.make_term(y, BVsort)
    equal = nodes.Equal(N = 4, delay = delay)
    res = equal.timing(x_,y_)
    assert res[0] == solver.make_term(max(x, y) + delay, BVsort)

@pytest.mark.parametrize(
    "N,s,x,y", 
    [(4, 1, 7, 8), (2, 0, 1, 0), (15, 1, 0, 96), (27, 0, 100, 1)])
def test_mux(N, s, x, y):
    BVN = solver.make_sort(BV, N)
    s_ = solver.make_term(s, solver.make_sort(BOOL))
    x_ = solver.make_term(x, BVN)
    y_ = solver.make_term(y, BVN)
    mux = nodes.Mux(N = N, delay = 0)
    res = mux(s_,x_,y_)
    assert res[0] == solver.make_term((x if s else y), BVN)

@pytest.mark.parametrize(
    "s,x,y,delay", 
    [(4, 1, 7, 8), (2, 0, 1, 0), (15, 1, 0, 96), (27, 0, 100, 1)])
def test_mux_delay(s, x, y, delay):
    BVsort = solver.make_sort(BV, 16)
    s_ = solver.make_term(s, BVsort)
    x_ = solver.make_term(x, BVsort)
    y_ = solver.make_term(y, BVsort)
    mux = nodes.Mux(N = 4, delay = delay)
    res = mux.timing(s_,x_,y_)
    assert res[0] == solver.make_term(max(s, x, y) + delay, BVsort)

@pytest.mark.parametrize(
    "N,d,init", 
    [(4, 1, 0), (2, 0, 1), (15, 96, 4), (27, 100, 20)])
def test_register(N, d, init):
    BVN = solver.make_sort(BV, N)
    d_ = solver.make_term(d, BVN)
    register = nodes.Register(N = N, init = init, setup = 0, hold = 0, output_delay = 0)
    res = register(d_)

    solver.push()
    n0 = solver.make_term(ops.Not, solver.make_term(ops.Equal, ur.at_time(res[0], 0), solver.make_term(init, BVN)))
    n1 = solver.make_term(ops.Not, solver.make_term(ops.Equal, ur.at_time(res[0], 1), d_))
    solver.assert_formula(solver.make_term(ops.Or, n0, n1))
    solver.assert_formula(ur.at_time(fts.init, 0))
    solver.assert_formula(ur.at_time(fts.trans, 0))
    sat = solver.check_sat()
    solver.pop()

    assert sat.is_unsat()

@pytest.mark.parametrize(
    "d,setup,hold,output_delay", 
    [(4, 1, 7, 3), (2, 0, 1, 5), (15, 1, 0, 100), (27, 0, 100, 3)])
def test_register_delay(d, setup, hold, output_delay):
    BVsort = solver.make_sort(BV, 16)
    d_ = solver.make_term(d, BVsort)
    register = nodes.Register(N = 4, init = 0, setup = setup, hold = hold, output_delay = output_delay)
    res = register.timing(d_)
    assert register.setup[0] == solver.make_term(d + setup, BVsort)
    assert register.hold[0] == solver.make_term(d - hold, BVsort)
    assert res[0] == solver.make_term(output_delay, BVsort)