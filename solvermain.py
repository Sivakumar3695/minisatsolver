from pyminsat.Solver import Solver

if __name__ == '__main__':
    solver = Solver()
    solver.add_problem_clause_db(['e', '-b', 'c'])
    solver.add_problem_clause_db(['a', '-d'])
    solver.add_problem_clause_db(['-a', 'd'])
    solver.add_problem_clause_db(['-a', '-d'])
    solver.add_problem_clause_db(['a', 'd'])
    model = solver.find_solution()
    if model is not None:
        print("Model Found")
        print(model)
    else:
        print("UnSat")
    print("Done")
