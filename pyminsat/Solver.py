from pyminsat.Clause import Clause
from pyminsat.Literals import Literals
from pyminsat.Variable import Variable


class Solver:
    def __init__(self):
        self._clauses = []
        self._learntclause = []
        self.__trail = []
        self.__traillimit = []
        self.__latestdecisionlevel = 0
        self._variablelist = []
        self._variableobjectlist = {}
        self._literalobjectlist = {}
        self.__propQ = []
        self._watches = {}
        self.__nlearntsallowed = 0

        self.__clauseinc = 1000
        self.__clausedecayfactor = 0.999

        self.__variableinc = 1000
        self.__variabledecayfactor = 0.95

    def add_problem_clause_db(self, literals):
        """
        add a clause of the CNF formula to the SAT solver problem

        :param
            literals String[]: Array of Strings
            example: ['a', '-b', 'c']
        :return: None
        """

        clause = Clause(self, literals, False)
        self._clauses.append(clause)

    def find_solution(self):
        """
        After adding the clause DB, solver.find_solution() can be called to find solution for the SAT problem.

        :param: None
        :return:
            model: if the solver is able to solve the SAT problem
            None: if the provided SAT CNF formula cannot be satisfied.
        """
        self.__nlearntsallowed = len(self._clauses) / 3
        if not self.__simplifyclausedb():
            return None
        return self.__solve()

    def _enqueue(self, lit, from_clause=None):
        """
        push the provided literal's variable into propQ.
        Note: Literals entering this method will be the last unassigned literal of the clause

        if variable of lit is already assigned a value
        [
            //return literal value based on the already assigned variable value
        ]
        else
        [
           //assign unassigned variable with a new value such that the from_clause evaluates to True.
           //update trial list
           //update propQ
        ]
        :param
            lit: literal for which the value is going to be provided. e.g : a
            from_clause: reason for clause assignment [i.e clause which forced this variable assignment through unit propagation]
        :return:
            1. True if the clause evaluates to True for the given literal assignment
            2. False otherwise.
        """
        var_obj = self._variableobjectlist[lit._varsymbol]
        if var_obj._value is not None:
            lit_val = self._valueOf(lit)
            if not lit_val:
                return False
            else:
                return True
        else:
            var_obj._value = not lit._negate
            var_obj._decisionlevel = self.__latestdecisionlevel
            var_obj._reason = from_clause
            self.__trail.append(var_obj._symbol)
            self.__propQ.append(var_obj._symbol)
            return True

    def __nAssigns(self):
        """
        :return: Number of variable assignments made so far
        """
        return len(self.__trail)

    def _getliteralobjectlist(self, lits):
        """
        Returns literal object list for the given list of literals in string format
        :param
            lits: String of literals.
            example: ['a', '-b', 'c']
        :return:
            will create a literal object for every literal provided and append it to a list.
            the list will be returned.
        """
        lit_obj_list = []
        for lit in lits:
            negate = lit.startswith("-")
            var_symbol = lit.replace('-', '') if negate else lit

            lit_obj = self._literalobjectlist.get(lit)
            if lit_obj is not None:
                lit_obj_list.append(lit_obj)
            else:
                lit_obj_list.append(Literals(self, var_symbol, negate))
        return lit_obj_list

    def __getliteralobject(self, lit):
        """
        Returns a literal object for the given literal in string format
        :param
            lit: A string literal
            examples: a , -b
        :return:
            Literals object type.
        """
        return self._variableobjectlist[lit]

    def _getvariableobject(self, var_symbol):
        """
        Returns a Variable object for the given variable in string format
        :param
            lit: A string variable
            examples: a , b
        :return:
            Variable object type.
        """
        return self._variableobjectlist[var_symbol]

    def _getoraddvariable(self, var_symbol):
        """
        Get a Variable object for the given variable string.
        if the variable is not present in solver._variableobjectlist, the variable object will be pushed to the list.
        :param
            var_symbol: a variable in string format
            examples: a, b
        :return:
            A Variable object type
        """
        if var_symbol in self._variablelist:
            return self._variableobjectlist[var_symbol]
        else:
            return Variable(self, var_symbol)

    def __simplifyclausedb(self):
        """
        This method will be called before entering solver.solve() to simplify the clauses in clause data base
        Following things will be checked to simplify the clause database:
            1. If any literal of a clause evaluated to True, clause will be removed
            2. If any literal of a clause evaluated to False, the literal will be remvoved as it is no longer useful
            3. If the clause is empty, the clause will be removed.
            4. If the clause is unit, the literal variable will be added to solver._propQ for unit propagation.
        :return:
            True by default
        """
        for clause in self._clauses:
            clause._simplify(solver=self)
        return True

    def __propagate(self):
        """
        This method will take the variables from the self.propQ (FIFO) until the queue is empty.
        For all the variables taken out,
            1. watch list of the variables will be made empty
            2. the clauses which are watched by the variables will be propagated.
                i.e clause.propagate() will be called for all those clauses
                clause.propagate() will return a clause if there is a conflict during the propagation.
                Otherwise, None will be returned

        In case of conflict,
            1. the rest of the clauses (the clauses that are not sent for propagation)
                will be added back to the watch list of the variable and
            2. propQ will be cleared

        :return:
            1. conflict clause in case of conflict
            2. otherwise,None
        """
        while len(self.__propQ) > 0:
            var = self.__propQ.pop(0)
            temp_clause_list = self._watches[var]
            self._watches[var] = []
            for i in range(0, len(temp_clause_list)):
                clause = temp_clause_list[i]
                no_conflict = clause._propagate(self, var)
                if not no_conflict:
                    for j in range(i + 1, len(temp_clause_list)):
                        self._watches[var].append(temp_clause_list[j])
                    self.__propQ.clear()
                    return clause

    def _valueOf(self, lit):
        """
        to get the value of the literal based on the assigned variable value.
        :param
            lit: Literal Object (note: do not pass literal string)
        :return:
            True / False
        """
        var_val = self._variableobjectlist[lit._varsymbol]._value
        return var_val if not lit._negate else not var_val

    def __recordlearntclause(self, learnt_lits):
        """
        A new clause will be created and added to the list of learnt clause in solver object.
        Note: All the learnt clause will be unit at the time of creation. Only the asserting variable will be unassigned
        Note: All the literal except asserting literal will be False at this point.
        Hence, the zeroth literal of the learnt clause will be pushed to solver.propQ for unit propagation.
        :param
            learnt_lits: Array of string literals
            example: ['a','-b','c']
        :return:
            None
        """
        clause = Clause(self, learnt_lits, True)
        self._enqueue(clause._lits[0], clause)
        if clause is not None:
            self._learntclause.append(clause)

    def __solve(self):
        """
        Basic solve method.
        This method will be called immediately after performing simplifyDB from find_solution() method.
        Flow:
        while(True)
        [
            #unit_propagation
            if conflict
            [
                #if conflict occurred at decision_level-0, return None (UN_SAT)
                1.analyse conlict
                2.back_track
                3.add_learnt_clause
                4.handle_decay_activities
            ]
            else
            [
                1.reduceDB if learnt cluase count crossed the limit
                2.if all variables are assigned with a value, return Model (SAT)
                3.otherwise, get next variable to assign value and proceed.
            ]
        ]
        :return:
            1. Model will be returned if the SAT problem can be satisfied
            2. None if the SAT problem cannot be satisfied
        """
        model = {}
        while True:
            conflict = self.__propagate()
            if conflict is not None:
                if self.__latestdecisionlevel == 0:
                    return None
                learnt_clause = []
                bt_level = self.__analyseconflict(conflict, learnt_clause)
                self.__canceluntil(bt_level)
                self.__recordlearntclause(learnt_clause)
                self.__handledecayactivities()
            else:
                if (len(self._learntclause) - self.__nAssigns()) >= self.__nlearntsallowed:
                    self.__reduceDB()
                if self.__nAssigns() == len(self._variablelist):
                    # model found
                    for var in self._variableobjectlist:
                        model[var] = self._variableobjectlist[var]._value if self._variableobjectlist[var]._value is not None else False
                    print(model)
                    return model
                else:
                    lit = self.__getmaximumactivityliteralobj()
                    self.__latestdecisionlevel = self.__latestdecisionlevel + 1
                    self.__assume(lit)

    def __analyseconflict(self, conflict, learnt_clause):
        """
        This method will compute
            1. the learnt_clause (i.e set of literals) that are responsible for the conflict
            2. the back-jumping level for the solver process.
        The method will be perform the followings:
            1. leave room for asserting literal
            2. push all the literals that forced the literals of the conflict clause to take the value assigned now.
            3. set learnt_clause[0] = asserting literal
        Detailed algorithmic description for step-2:
            counter = 0;
            do
            [
                1. reason = conflict_clause._calculatereason(p)
                    //for the first iteration, conflict_clause will be the clause passed to this method
                    //for further iterations, conflict_clause = the reason for one of the literals in the learnt_clause
                2. for all the literals of the reason:
                    [
                        //seen[lit] == True will mean that the literal is already iterated for the leant_cla computation
                        // hence, it should not be iterated again
                        if (!seen[lit])
                        [
                           seen[lit] = True;
                           if lit.decision_level() == current_decision_level
                                //if the literal is assigned a value in the current decision level,
                                //the computation of reason for it is necessary.
                                counter++;
                           else if q.decision_level > 0
                                //zeroth decision level literals cannot be in learnt_clause
                                //because those are not assigned a value based on any assumption
                                learnt_clause.push(lit)
                                bt_level = max(bt_level, lit.decision_level)
                        ]
                    ]
                    //pick the next variable for conflict reason analysis:
                    do
                    [
                        p = the last assigned variable
                        conflict = p.reason
                        undoone() //to reset and pop the last assigned variable in trail list
                    ]while (!seen[p]) //only literals with (seen[p]=True) can be the next literal for conflict analysis
            ]while(counter > 0)
            NOte : p will be the asserting literal.
                    The value of 'p' present while breaking the condition counter > 0 will be the asserting literal.
        :param
            conflict: A Clause object - the conflict clause found during the propagation process
        :param
            learnt_clause: an empty list
            when this method is completed,
            This list will be filled with values and will be Array of literals in str format. Example: ['a', '-b', 'c']
        :return:
            bt_level - A number. i.e backtracking level to jump back to resolve the conflict
        """
        counter = 0
        p = None
        p_lit = None
        p_reason = []
        seen = {}

        learnt_clause.append(None)
        bt_level = 0

        while True:
            p_reason = []
            conflict._calculatereason(self, p, p_reason)
            for i in range(0, len(p_reason)):
                q = p_reason[i]
                if seen.get(q._varsymbol) is None or seen[q._varsymbol].get('seen') is False:
                    seen[q._varsymbol] = {'seen': True, 'negate': q._negate}
                    var_obj = self._getvariableobject(q._varsymbol)
                    if var_obj._decisionlevel == self.__latestdecisionlevel:
                        counter = counter + 1
                        if var_obj._reason is None:
                            bt_level = var_obj._decisionlevel
                    elif var_obj._decisionlevel > 0:
                        l_clause_lit = q._varsymbol if seen[q._varsymbol].get('negate') is False else '-' + q._varsymbol
                        learnt_clause.append(l_clause_lit)
                        bt_level = max(bt_level, var_obj._decisionlevel)
            while True:
                p = self.__trail[len(self.__trail) - 1]
                var_obj = self._getvariableobject(p)
                conflict = var_obj._reason
                self.__undoone()
                if seen.get(p) is not None and seen[p].get('seen') is True:
                    p_lit = p if seen[p].get('negate') is False else '-' + p
                    break
            counter = counter - 1
            if counter == 0:
                break
        learnt_clause[0] = p_lit
        return bt_level

    def __handledecayactivities(self):
        """
        Activities of variables and clauses will be reduced by multiplying  the corresponding factors
        :return: None
        """
        self.__variableinc = self.__variableinc * self.__variabledecayfactor
        self.__clauseinc = self.__clauseinc * self.__clausedecayfactor

    def __assume(self, lit_obj):
        """
        1. solver.__traillimit will be pushed with the previous decision level's trial limit
        2. literal passed will be provided to enqueue and it will be added to solver.propQ
        :param
            lit_obj: Literal Object (note: do not pass literal string)
        :return: None
        """
        self.__traillimit.append(len(self.__trail))
        self._enqueue(lit_obj)

    def _bumpclauseactivity(self, clause):
        """
        activity of the given clause will be increased by adding the solver.__clauseinc factor
        :param
            clause: A clause object
        :return: None
        """
        clause.clause_activity = clause.clause_activity + self.__clauseinc

    def __bumpvariableactivity(self, lit_obj):
        """
        acitivty of the given variable will be increased by adding the solver.__variableinc factor
        :param
            lit_obj: A literal Object (note: do not pass literal string)
        :return:
        """
        lit_obj._variableactivity = lit_obj._variableactivity + self.__variableinc

    def __getmaximumactivityliteralobj(self):
        """
        Use this method to get an unassigned variable with highest activity.
        :return: A variable object (note: the return data type will not be a variable string)
        """
        max_activity = 0
        out_lit_obj = None
        for var in self._literalobjectlist:
            lit_obj = self._literalobjectlist[var]
            var_obj = self._variableobjectlist[lit_obj._varsymbol]
            if lit_obj._variableactivity > max_activity and var_obj._value is None:
                max_activity = lit_obj._variableactivity
                out_lit_obj = lit_obj
        return out_lit_obj

    def __reduceDB(self):
        """
        This method will perform the below actions:
            1. Sort the learnt clauses based on their clause_activity
            2. Remove half of the learnt clause:
                i. if not locked i.e the clause is not the reason for cluase.lits[0]
                Note: The clause will be the reason for clause.lits[0]
                        if and only if it forces the lits[0] to take a value through unit propagation
            3. Also, remove the learnt clauses if their activity is below a certain limit.
                The limit will be based on clauseinc and sizeof(leantclause)
        :return: None
        """
        i = 0
        cla_lim = self.__clauseinc / len(self._learntclause)

        self._learntclause.sort(key=_getkeyforclausesort, reverse=False)
        while i < len(self._learntclause) / 2:
            l_cla = self._learntclause[i]
            if not l_cla._islocked(self):
                l_cla._removeclause(self)
            i = i + 1
        while i < len(self._learntclause):
            l_cla = self._learntclause[i]
            if not l_cla.is_locked(self) and l_cla.clause_activity < cla_lim:
                l_cla._removeclause(self)

    def __undoone(self):
        """
        The last assigned variable will be unassigned by resetting the followings:
            1. variable.value
            2. variable.decision_level
            3. variable.reason
        Note: The last unassigned variable will be fetched from solver.__trail
        :return: None
        """
        var = self.__trail.pop()
        var_obj = self._variableobjectlist[var]
        var_obj._value = None
        var_obj._decisionlevel = -1
        var_obj._reason = None

    def __canceluntil(self, bt_level):
        """
        This method will be useful for performing back-jumping.
        All the decision level until the given bt_level will be undone

        :param
            bt_level: A number (i.e decision_level)
        :return: None
        """
        while self.__latestdecisionlevel > bt_level:
            self.__cancelonelevel()

    def __cancelonelevel(self):
        """
        All the Assignments made in one decision level will be undone in this method
            1. solver.__latestdecisionlevel will be reduced by 1.
            2. pop the solver.__traillimit stack.

        Explanation for computation of c:
        self.__trail = nAssign() so far [say for example: 9]
        self.__traillimit[last] = nAssign() till the previous decision level [say for example: 6]
        Hence, c = 3 (i.e 3 assignments after the previous decision level).

        :return: None
        """
        c = len(self.__trail) - self.__traillimit[len(self.__traillimit) - 1]
        while c != 0:
            self.__undoone()
            c = c - 1
        self.__latestdecisionlevel = self.__latestdecisionlevel - 1
        self.__traillimit.pop()


def _getkeyforclausesort(obj):
    """
    Clauses will be sorted based on the clause activity
    :param obj:
    :return:
    """
    return obj.clause_activity
