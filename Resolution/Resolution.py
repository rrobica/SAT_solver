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
    Performs resolution with limits on iterations and overall clause count.
    Returns:
      - False if an empty clause is derived (unsat),
      - True if resolution completes with no new clauses (suggesting SAT),
      - None if it hits an iteration or clause count limit.
    """
    new_clauses = set(map(tuple, clauses))
    iteration = 0
    while iteration < max_iterations:
        iteration += 1
        
        # If too many clauses are generated, bail out.
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
        # If no new resolvents were generated, return SAT.
        if not generated.difference(new_clauses):
            return True
        new_clauses |= generated
    # If we reach here, the limit was reached.
    return None

def davis_putnam(clauses):
    while clauses:
        literals = {l for clause in clauses for l in clause}
        # Pure literal elimination.
        for l in literals:
            if -l not in literals:
                clauses = [c for c in clauses if l not in c]
                break
        if not clauses:
            return True
        # Unit clause propagation.
        unit_clauses = [c[0] for c in clauses if len(c) == 1]
        for u in unit_clauses:
            clauses = [list(filter(lambda x: x != -u, c)) for c in clauses if u not in c]
        else:
            var = abs(next(iter(literals)))
            return davis_putnam([[v for v in c if v != -var] for c in clauses if var not in c]) or \
                   davis_putnam([[v for v in c if v != var] for c in clauses if -var not in c])
    return False

def dpll(clauses, assignment={}, deadline=None):
    """
    Basic DPLL with a check against a deadline (timestamp).
    Every recursive call checks if the timeout has been reached.
    """
    if deadline is not None and time.time() > deadline:
        raise TimeoutError("DPLL timeout reached")
        
    if not clauses:  # All clauses satisfied.
        return True, assignment
    if [] in clauses:  # Empty clause found.
        return False, {}
    
    literals = {l for clause in clauses for l in clause}
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
    
    # Choose a literal (variable) and branch.
    var = next(iter(literals))
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
    Generates a random clause (list of literals).
    Clause length is chosen randomly between 3 and min(10, num_literals).
    """
    clause_size = random.randint(3, min(10, num_literals))
    clause = random.sample(range(1, num_literals + 1), k=clause_size)
    clause = [lit if random.choice([True, False]) else -lit for lit in clause]
    return clause

def solve_sat_with_all_methods(formula):
    # Try resolution first
    start_time = time.time()
    result_res = resolution_algorithm(formula, max_iterations=3, max_clauses=5000)
    elapsed_res = time.time() - start_time

    # Try Davis-Putnam (DP)
    start_time = time.time()
    result_dp = davis_putnam(formula)
    elapsed_dp = time.time() - start_time

    # Try DPLL as a fallback
    start_time = time.time()
    result_dpll, _ = dpll_with_timeout(formula, timeout=5)
    elapsed_dpll = time.time() - start_time

    return {
        "Resolution": (result_res, elapsed_res),
        "Davis-Putnam": (result_dp, elapsed_dp),
        "DPLL": (result_dpll, elapsed_dpll)
    }


def generate_random_formula(num_clauses, num_literals, unsat_injection_probability=0.3):
    """
    Generates a CNF formula as a list of clauses.
    With a given probability, forces unsatisfiability by adding a pair of contradictory unit clauses.
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

# --- SAT Solver Selector and File Output ---

def solve_sat(formula):
    """
    Tries to solve the given formula with Resolution first.
    If resolution reaches its limits, it falls back to DPLL (with a timeout).
    Returns a tuple:
       (algorithm_used, result (True for SAT, False for UNSAT, or "TIMEOUT"), runtime)
    """
    start_time = time.time()
    result_res = resolution_algorithm(formula, max_iterations=3, max_clauses=5000)
    elapsed_res = time.time() - start_time

    if result_res is not None:
        return ("Resolution", result_res, elapsed_res)
    else:
        start_time = time.time()
        result_dpll, _ = dpll_with_timeout(formula, timeout=5)
        elapsed_dpll = time.time() - start_time
        if result_dpll is None:
            return ("DPLL", "TIMEOUT", elapsed_dpll)
        return ("DPLL", result_dpll, elapsed_dpll)

def save_results_to_file(filename, formulas):
    with open(filename, 'w') as f:
        for idx, formula in enumerate(formulas, start=1):
            algorithm_used, result, runtime = solve_sat(formula)
            f.write(f"Formula #{idx}: {formula}\n")
            f.write(f"Algorithm: {algorithm_used}, Result: {result}, Runtime: {runtime:.4f} seconds\n")
            f.write("-" * 50 + "\n")
    print(f"Results saved to {filename}")

def main():
    num_formulas = 20    # How many CNF formulas to generate.
    num_clauses = 20     # Clauses per formula.
    num_literals = 10    # Variables in range 1 to num_literals.
    unsat_prob = 0.3     # Chance to inject contradictory unit clauses.
    
    formulas = [generate_random_formula(num_clauses, num_literals, unsat_prob)
                for _ in range(num_formulas)]
    save_results_to_file("sat_results.txt", formulas)

if __name__ == "__main__":
    main()
