# MiniSat solver

This project can be used to check if the given SAT problem (CNF format) can be satisfied or not. If it can be satisfied, a model for the SAT problem will be printed.

The project is designed in such a way that the SAT problem has to be entered in the solvermain.py file. On running this python file, the SAT problem entered will be evaluated.

# Steps to initialise the CNF formula for SAT solving:
1. Create an object of Solver

    solver = new Solver();
2. Every clause in the CNF formula has to be added to the solver object through add_problem_clause_db()

    The parameter for the add_problem_clause_db() is the arrays of literals in str format.
    
    example: solver.add_problem_clause_db(['a', '-b', 'c'])
    
    Note: This will be treated as case-insensitive. Hence, upper and lower cases will be treated as the same literal.
3. After adding all the clauses of the given SAT CNF formula, solver method can be called to check if solution exists for the given formula.

    **solver.find_solution()** will handle this evaluation process.

# Input: CNF Formula
  
  ### Sample-1 : Satisfiable problem
  
  For the CNF formula: (e | -b | c) & (a | -d) & (-a | d) & (-a | -d)
  
  solvermain.py main method:

    solver = Solver()
    solver.add_problem_clause_db(['e', '-b', 'c'])
    solver.add_problem_clause_db(['a', '-d'])
    solver.add_problem_clause_db(['-a', 'd'])
    solver.add_problem_clause_db(['-a', '-d'])
    model = solver.find_solution()
    
  ### Sample-2 : UnSatisfiable problem

  For the CNF formula: (e | -b | c) & (a | -d) & (-a | d) & (-a | -d) & (a & d)
  
  solvermain.py main method:
    
    solver = Solver()
    solver.add_problem_clause_db(['e', '-b', 'c'])  
    solver.add_problem_clause_db(['a', '-d'])
    solver.add_problem_clause_db(['-a', 'd'])
    solver.add_problem_clause_db(['-a', '-d'])
    solver.add_problem_clause_db(['a', 'd'])
    model = solver.find_solution()

# Model Output evaluation 

  If the model is empty (i.e None)

    The problem is unsatisfiable. 
    Output will be : UnSAT
  Else

    The problem is satifiable and has a model:
    Output will be: Model Found and model will be printed
    
  ### Output for Sample-1

    {'e': True, 'b': False, 'c': True, 'a': False, 'd': False}
    Model Found
    {'e': True, 'b': False, 'c': True, 'a': False, 'd': False}
    MiniSat solving completed

    Process finished with exit code 0
    
  ### Output for Sample-2
    
    UnSat
    MiniSat solving completed

    Process finished with exit code 0
