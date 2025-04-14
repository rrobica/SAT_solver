import random
import time
from itertools import combinations

# --- SAT Solvers ---

def resolve(clause1, clause2):
    for literal in clause1:
        if -literal in clause2:
            new_clause = set(clause1) | set(clause2)
            new_clause.discard(literal)
            new_clause.discard(-literal)
            return list(new_clause)
    return None

def resolution_algorithm(clauses, max_iterations=3, max_clauses=5000):
    """
    Naively performs resolution with an iteration limit.
    Returns:
      - False if an empty clause is derived (unsat),
      - True if resolution completes with no new clauses (suggesting SAT),
      - None if it hits an iteration or clause count limit.
    """
    new_clauses = set(map(tuple, clauses))
    iteration = 0
    while iteration < max_iterations:
        iteration += 1
        if len(new_clauses) > max_clauses:
            print(f"Resolution: Too many clauses ({len(new_clauses)}) at iteration {iteration}. Aborting resolution.")
            return None
        new_pairs = list(combinations(new_clauses, 2))
        generated = set()
        for clause1, clause2 in new_pairs:
            resolvent = resolve(list(clause1), list(clause2))
            if resolvent is not None:
                if not resolvent:  # Empty clause found: unsat
                    return False
                generated.add(tuple(sorted(resolvent)))
        if not generated.difference(new_clauses):
            return True
        new_clauses |= generated
    return None

def davis_putnam(clauses):
    while clauses:
        # If any clause is empty, the formula is unsat.
        if any(c == [] for c in clauses):
            return False

        # Build the set of all literals in the formula.
        literals = {l for clause in clauses for l in clause}
        # If no literals remain, the formula is trivially satisfied.
        if not literals:
            return True
        
        # Pure literal elimination.
        pure_literal_found = False
        for l in literals:
            if -l not in literals:
                clauses = [c for c in clauses if l not in c]
                pure_literal_found = True
                break
        if pure_literal_found:
            if not clauses:
                return True
            continue  # Restart the while loop with updated clauses

        # Unit clause propagation.
        unit_clauses = [c[0] for c in clauses if len(c) == 1]
        if unit_clauses:
            for u in unit_clauses:
                clauses = [list(filter(lambda x: x != -u, c)) for c in clauses if u not in c]
            if not clauses:
                return True
            continue  # Restart the while loop with updated clauses

        # Before branching, ensure there are literals left.
        if not literals:
            return True
        
        # Choose a variable for branching.
        var = abs(next(iter(literals)))
        # Recursively check both branches.
        left = davis_putnam([[v for v in c if v != -var] for c in clauses if var not in c])
        right = davis_putnam([[v for v in c if v != var] for c in clauses if -var not in c])
        return left or right

    return False

def dpll(clauses, assignment={}, deadline=None):
    if deadline is not None and time.time() > deadline:
        raise TimeoutError("DPLL timeout reached")
    if not clauses:  # All clauses satisfied.
        return True, assignment
    if [] in clauses:  # Found an empty clause.
        return False, {}
    
    literals = {l for clause in clauses for l in clause}
    if not literals:
        return True, assignment
    
    # Pure literal elimination.
    for l in literals:
        if -l not in literals:
            new_clauses = [c for c in clauses if l not in c]
            return dpll(new_clauses, {**assignment, l: True}, deadline=deadline)

    # Unit propagation.
    unit_clauses = [c[0] for c in clauses if len(c) == 1]
    if unit_clauses:
        u = unit_clauses[0]
        new_clauses = [list(filter(lambda x: x != -u, c)) for c in clauses if u not in c]
        return dpll(new_clauses, {**assignment, u: True}, deadline=deadline)

    var = abs(next(iter(literals)))
    sat_true, assgn_true = dpll([[v for v in c if v != -var] for c in clauses if var not in c],
                                 {**assignment, var: True}, deadline=deadline)
    if sat_true:
        return True, assgn_true
    return dpll([[v for v in c if v != var] for c in clauses if -var not in c],
                {**assignment, var: False}, deadline=deadline)

def dpll_with_timeout(clauses, assignment={}, timeout=5):
    """
    Wrapper for DPLL that uses a timeout.
    If DPLL does not complete within 'timeout' seconds, returns (None, {}).
    """
    deadline = time.time() + timeout
    try:
        return dpll(clauses, assignment, deadline=deadline)
    except TimeoutError:
        return None, {}

# --- Random Formula Generator ---

def generate_random_clause(num_literals):
    """
    Generates a random clause (without the terminating 0).
    The clause length is randomly chosen between 3 and min(10, num_literals).
    """
    clause_size = random.randint(3, min(10, num_literals))
    clause = random.sample(range(1, num_literals + 1), k=clause_size)
    clause = [lit if random.choice([True, False]) else -lit for lit in clause]
    return clause

def generate_random_formula(num_clauses, num_literals, unsat_injection_probability=0.3):
    """
    Generates a CNF formula as a list of clauses.
    Optionally forces unsatisfiability by adding contradictory unit clauses.
    """
    formula = []
    for _ in range(num_clauses):
        clause = generate_random_clause(num_literals)
        formula.append(clause)
    if random.random() < unsat_injection_probability:
        v = random.randint(1, num_literals)
        formula.append([v])
        formula.append([-v])
    return formula

# --- SAT Solver Comparison Function ---

def solve_sat_with_all_methods(formula):
    """
    Runs all three algorithms (Resolution, Davis-Putnam, DPLL) on the given formula.
    Returns a dictionary with (result, runtime) for each algorithm.
    """
    results = {}

    # Resolution
    start_time = time.time()
    result_res = resolution_algorithm(formula, max_iterations=3, max_clauses=5000)
    elapsed_res = time.time() - start_time
    results["Resolution"] = (result_res, elapsed_res)

    # Davis-Putnam
    start_time = time.time()
    result_dp = davis_putnam(formula)
    elapsed_dp = time.time() - start_time
    results["Davis-Putnam"] = (result_dp, elapsed_dp)

    # DPLL
    start_time = time.time()
    result_dpll, _ = dpll_with_timeout(formula, timeout=5)
    elapsed_dpll = time.time() - start_time
    results["DPLL"] = (result_dpll, elapsed_dpll)

    return results

# --- File Output ---

def save_results_to_file(filename, formulas):
    """
    For each generated formula, runs Resolution, Davis-Putnam, and DPLL,
    then writes the results into the specified file.
    """
    with open(filename, 'w') as f:
        for idx, formula in enumerate(formulas, start=1):
            results = solve_sat_with_all_methods(formula)
            f.write(f"Formula #{idx}: {formula}\n")
            for algo, (result, runtime) in results.items():
                r_str = 'SAT' if result is True else ('NOT SAT' if result is False else 'TIMEOUT')
                f.write(f"{algo}: {r_str}, Runtime: {runtime:.4f} seconds\n")
            f.write("-" * 50 + "\n")
    print(f"Results saved to {filename}")

# --- Main Function ---

def main():
    num_formulas = 10    # Number of CNF formulas to generate.
    num_clauses = 20     # Number of clauses per formula.
    num_literals = 10    # Variables are in the range [1, num_literals].
    unsat_prob = 0.3     # Probability to inject contradictory unit clauses.

    formulas = [generate_random_formula(num_clauses, num_literals, unsat_prob)
                for _ in range(num_formulas)]
    save_results_to_file("sat_results_comparison.txt", formulas)

if __name__ == "__main__":
    main()