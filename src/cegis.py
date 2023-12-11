import itertools
import smt_switch.primops as pops
from smt_switch.sortkinds import BOOL, BV

class Cegis():
    def __init__(self, solver, synth_base, synth_constrain, verify, E_vars, A_vars, D_vars):
        self.solver = solver
        self.synth_base = synth_base
        self.synth_constrain = synth_constrain
        self.verify = verify
        self.E_vars = E_vars
        self.A_vars = A_vars
        self.D_vars = D_vars

    def run(self):
        # TODO edit this function to make better use of incremental solving
        synth_constrain = self.solver.make_term(1, self.solver.make_sort(BOOL))
        for i in itertools.count(1):
            # synthesize step
            self.solver.push()
            self.solver.assert_formula(self.synth_base)
            self.solver.assert_formula(synth_constrain)
            res = self.solver.check_sat()
            self.solver.pop()
            if res.is_unsat():
                return None

            # verify step
            E_vals = {var:self.solver.get_value(var) for var in self.E_vars}
            self.solver.push()
            self.solver.assert_formula(self.solver.make_term(pops.Not, self.solver.substitute(self.verify, E_vals)))
            res = self.solver.check_sat()
            self.solver.pop()
            if res.is_unsat():
                return E_vals
            
            A_vals = {var:self.solver.get_value(var) for var in self.A_vars}
            new_D_vars = {var:self.solver.make_symbol(f"{str(var)}@{i}", var.get_sort()) for var in self.D_vars}
            mapping = {**A_vals, **new_D_vars}
            new_constraint = self.solver.substitute(self.synth_constrain, mapping)
            synth_constrain = self.solver.make_term(pops.And, synth_constrain, new_constraint)
