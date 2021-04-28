class Literals:
    def __init__(self, solver, var, negate=False):
        self._varsymbol = solver._getoraddvariable(var)._symbol
        self._negate = negate
        lit_symbol = '-' + self._varsymbol if negate else self._varsymbol
        solver._literalobjectlist[lit_symbol] = self
        solver._setliteralactivityinliteralinit(self)

    def _isnegationexists(self, lits_obj_list):
        """
        Check if the a literal and its negation exists in the given lits list
        :param lits_obj_list: A literal object list. (Note: Do not pass the list with literals in str format)
        :return:
            1. True if a literal and its negation exists
            2. False otherwise.
        """
        for lit in lits_obj_list:
            if lit._varsymbol == self._varsymbol and lit._negate != self._negate:
                return True
        return False
