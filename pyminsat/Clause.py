class Clause:
    def __init__(self, solver, lits, is_learnt):
        self._lits = solver._getliteralobjectlist(lits)
        self.__learnt = is_learnt
        if not is_learnt:
            if self._simplify(solver):
                return
        if len(self._lits) == 1:
            # if no. of literals is 1, the clause can be unit-propagated
            solver._enqueue(self._lits[0], self)
        else:
            # add the clauses to the watches list of lits[0] and lits[1]
            solver._watches[self._lits[0]._varsymbol].append(self)
            solver._watches[self._lits[1]._varsymbol].append(self)
            solver._bumpvariableactivity(self._lits[0])
            if is_learnt:
                # if the clause is learnt,
                # its activity and its literals' activities can be bumped while adding the clause
                solver._bumpclauseactivity(self)
                for i in range(1, len(self._lits)):
                    lit = self._lits[i]
                    solver._bumpvariableactivity(lit)
                return
            solver._clauses.append(self)
    clause_activity = 1


    def _simplify(self, solver):
        """
        This method is used to simply a clause by doing the followings:
            1. if there is no literals, the clause will be empty and can be removed.
            2. if any literal is True, the clause can be removed as it will evaluate to True in zeroth decision level
            3. Remove any literal that evaluates to False during initialisation as it will not be useful
            4. If a literal and its negation exists in the same clause,
                the clause can be removed as it will definitely evaluate to True in zeroth decision level.
        :param solver: A solver object
        :return:
            1. True if the clause is removed from solver object
            2. False otherwise
        """
        if len(self._lits) == 0:
            print("Empty clause. Hence, it will be removed.")
            return True
        for lit in self._lits:
            # if any of the literal evaluates to True, we can remove whole clause itself
            if solver._valueOf(lit):
                return True
            # id p and ~p exists in the same clause, the clause can be removed
            elif lit._isnegationexists(self._lits):
                return True
            elif solver._valueOf(lit) is False:
                self._lits.remove(lit)  # false literals can be removed as it will be of no use for the clause.
                return len(self._lits) == 0
        return False

    def __swap(self, index_1, index_2):
        """
        This method will swap the literals in index_1 and index_2 of the clause.lits[] array
        :param index_1: A number
        :param index_2: A number
        :return: None
        """
        temp = self._lits[index_1]
        self._lits[index_1] = self._lits[index_2]
        self._lits[index_2] = temp

    def _propagate(self, solver, var):
        """
        This method is used to propagate a clause after a variable watching it is assigned a value.

        This function in simple:
            1. if valueOf(lits[0]) is True:
                add the clause back to variable's watches list.
                return True

            NOTE: It is always expected that the lits[0] should evaluate to True.
                    Hence, if lits[0] evaluated to False in any case, swap lits[0] and lits[1]

            2. if the passed variable is in lits[0] and it evaluates to False:
                swap lits[0] and lits[1]
            3. else if the passed variable is in lits[1] and it evaluates to True:
                swap lits[0] and lits[1]
                return True
            4. Find any other literal that is not false.
                If Found, swap that literal and lits[1]
                return True
            5. If the function reaches this point, only lits[0] is the only unassigned in this clause
                Hence, enqueue lits[0] and pass it for unit propagation.

        :param solver: A solver object
        :param var: a variable symbol in str format
        :return:
            1. False if and only if the lits[0] is already assigned a value
                and evaluates to False during solver.enqueue() call
                As that would result in the whole clause taking False value.
            2. True otherwise
        """
        if solver._valueOf(self._lits[0]):
            solver._watches[var].append(self)
            return True
        elif len(self._lits) == 1:
            # in case of unit clause, if lit[0] evaluates to False, it results in conflict.
            solver._watches[var].append(self)
            return False
        if self._lits[0]._varsymbol == var and solver._valueOf(self._lits[0]) is False:
            # print(self.__learnt)
            self.__swap(0, 1)
        elif self._lits[1]._varsymbol == var and solver._valueOf(self._lits[1]) is True:
            self.__swap(0, 1)
            solver._watches[var].append(self)
            return True
        for i in range(2, len(self._lits)):
            if solver._valueOf(self._lits[i]) is not False:
                self.__swap(i, 1)
                solver._watches[self._lits[1]._varsymbol].append(self)
                if solver._valueOf(self._lits[1]):
                    self.__swap(1, 0)
                return True
        # unit_propagation
        solver._watches[var].append(self)
        return solver._enqueue(self._lits[0], self)

    def _islocked(self, solver):
        """
        This method will return if the clause is responsible for its lits[0] value.
        i.e if this clause forced the lits[0] to take a value through unit propagation.
        :param solver: A solver object
        :return:
            1. True if the clause is the reason for its lits[0]
            2. False otherwise.
        """
        var_obj = solver._getvariableobject(self._lits[0]._varsymbol)
        return var_obj._reason == self

    def _calculatereason(self, solver, lit, reason):
        """
        This method will append all the literals of this clause to reason_list param if lit param is empty
        If the lit param is not empty, all the literals except the lits[0] will be appended to the reason_list param

        The basic idea of this method is:
         => the lits[0] is forced to take a value after all the other literals of this clause is false.
         => Hence, lits[0]'s reason is all the other literals of this clause.

        If the clause if learnt, its activity can be bumped.

        :param solver: A solver object.
        :param
            lit: can be
                -> empty or
                -> a single literal [However, this literal should be the lits[0]. Otherwise, alogrithm could go wrong]
        :param
            reason: An empty list.
                    This list will be filled with the literals of this clause.
        :return: None.
        """
        start = 0 if lit is None else 1
        for i in range(start, len(self._lits)):
            reason.append(self._lits[i])
        if self.__learnt:
            solver._bumpclauseactivity(self)

    def _removeclause(self, solver):
        """
        This method is used to remove a learnt clause.
        Before removing a learnt clause, the clause must be removed from the watches list of its lits[0] and lits[1]
        :param solver: A solver object
        :return: None
        """
        if not self.__learnt:
            return
        solver._watches[self._lits[0]._varsymbol].remove(self)
        if len(self._lits) > 1:
            solver._watches[self._lits[1]._varsymbol].remove(self)
        solver._learntclause.remove(self)
