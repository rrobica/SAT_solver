from itertools import combinations

def resolve(clause1, clause2):
    for literal in clause1:
        if -literal in clause2:
            new_clause = set(clause1) | set(clause2)
            new_clause.discard(literal)
            new_clause.discard(-literal)
            return list(new_clause)
    return None

def resolution_algorithm(clauses):
    new_clauses = set(map(tuple, clauses))
    while True:
        new_pairs = list(combinations(new_clauses, 2))
        generated = set()
        for clause1, clause2 in new_pairs:
            resolvent = resolve(list(clause1), list(clause2))
            if resolvent is not None:
                if not resolvent:  # Empty clause means unsatisfiable
                    return False
                generated.add(tuple(resolvent))
        if generated.issubset(new_clauses):
            return True  # No new clauses, SAT remains undetermined
        new_clauses |= generated
def davis_putnam(clauses):
    while clauses:
        literals = {l for clause in clauses for l in clause}
        for l in literals:
            if -l not in literals:
                clauses = [c for c in clauses if l not in c]
                break
        if not clauses:
            return True
        unit_clauses = [c[0] for c in clauses if len(c) == 1]
        for u in unit_clauses:
            clauses = [list(filter(lambda x: x != -u, c)) for c in clauses if u not in c]
        else:
            var = abs(next(iter(literals)))
            return davis_putnam([[v for v in c if v != -var] for c in clauses if var not in c]) or \
                   davis_putnam([[v for v in c if v != var] for c in clauses if -var not in c])
    return False
def dpll(clauses, assignment={}):
    if not clauses:
        return True, assignment
    if [] in clauses:
        return False, {}
    
    literals = {l for clause in clauses for l in clause}
    for l in literals:
        if -l not in literals:
            new_clauses = [c for c in clauses if l not in c]
            return dpll(new_clauses, {**assignment, l: True})
    
    unit_clauses = [c[0] for c in clauses if len(c) == 1]
    for u in unit_clauses:
        new_clauses = [list(filter(lambda x: x != -u, c)) for c in clauses if u not in c]
        return dpll(new_clauses, {**assignment, u: True})
    
    var = next(iter(literals))
    return dpll([[v for v in c if v != -var] for c in clauses if var not in c], {**assignment, var: True}) or \
           dpll([[v for v in c if v != var] for c in clauses if -var not in c], {**assignment, var: False})
import random

def generate_random_clause(num_literals):
    clause_size = random.randint(3, min(10, num_literals))
    clause = random.sample(range(1, num_literals + 1), k=clause_size)
    clause = [lit if random.choice([True, False]) else -lit for lit in clause]
    clause.append(0)  # Clause terminator
    return clause

def save_results_to_file(filename, clauses):
    with open(filename, 'w') as f:
        for clause in clauses:
            result = dpll([clause[:-1]])[0]  # Evaluate single clause
            f.write(f"Clause: {clause[:-1]} Result: {'SAT' if result else 'NOT SAT'}\n")

def main():
    num_clauses, num_literals = 20, 10
    all_clauses = [generate_random_clause(num_literals) for _ in range(num_clauses)]
    save_results_to_file("sat_results.txt", all_clauses)
    print("Results saved to sat_results.txt")

if __name__ == "__main__":
    main()