class Variable:
    def __init__(self, solver, symbol):
        self._symbol = symbol
        self._value = None
        self._reason = None
        self._decisionlevel = 0
        if symbol not in solver._variablelist:
            solver._variablelist.append(symbol)
            solver._variableobjectlist[symbol] = self
            solver._watches[symbol] = []
