import random
import time
from itertools import combinations
import sys
import psutil
import os
import gc
import random

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
    Aplica metoda rezoluției într-un mod naive, cu limită de iterații și număr maxim de clauze.
    Returnează:
      - False dacă se derivă clauza vidă (formula este nesatisfiabilă),
      - True dacă rezoluția se termină fără clauze noi (sugerează satisfiabilitate),
      - None dacă se atinge limita de iterații/clauze.
    """
    new_clauses = set(map(tuple, clauses))
    iteration = 0
    while iteration < max_iterations:
        iteration += 1
        if len(new_clauses) > max_clauses:
            print(f"Rezoluție: Prea multe clauze ({len(new_clauses)}) la iterația {iteration}. Oprirea rezoluției.")
            return None
        new_pairs = list(combinations(new_clauses, 2))
        generated = set()
        for clause1, clause2 in new_pairs:
            resolvent = resolve(list(clause1), list(clause2))
            if resolvent is not None:
                if not resolvent:  # Clauza vidă: nesatisfiabil
                    return False
                generated.add(tuple(sorted(resolvent)))
        if not generated.difference(new_clauses):
            return True
        new_clauses |= generated
    return None

def davis_putnam(clauses):
    while clauses:
        if any(c == [] for c in clauses):
            return False
        literals = {l for clause in clauses for l in clause}
        if not literals:
            return True
        pure_literal_found = False
        for l in literals:
            if -l not in literals:
                clauses = [c for c in clauses if l not in c]
                pure_literal_found = True
                break
        if pure_literal_found:
            if not clauses:
                return True
            continue
        unit_clauses = [c[0] for c in clauses if len(c) == 1]
        if unit_clauses:
            for u in unit_clauses:
                clauses = [list(filter(lambda x: x != -u, c)) for c in clauses if u not in c]
            if not clauses:
                return True
            continue
        if not literals:
            return True
        var = abs(next(iter(literals)))
        left = davis_putnam([[v for v in c if v != -var] for c in clauses if var not in c])
        right = davis_putnam([[v for v in c if v != var] for c in clauses if -var not in c])
        return left or right
    return False

def dpll(clauses, assignment={}, deadline=None):
    if deadline is not None and time.time() > deadline:
        raise TimeoutError("Timpul alocat DPLL a expirat")
    if not clauses:
        return True, assignment
    if [] in clauses:
        return False, {}
    literals = {l for clause in clauses for l in clause}
    if not literals:
        return True, assignment
    for l in literals:
        if -l not in literals:
            new_clauses = [c for c in clauses if l not in c]
            return dpll(new_clauses, {**assignment, l: True}, deadline=deadline)
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
    deadline = time.time() + timeout
    try:
        return dpll(clauses, assignment, deadline=deadline)
    except TimeoutError:
        return None, {}

# --- Generatorul de formule random ---
    
def generate_random_clause(num_literals):
    """
    Generează o clauză random (fără terminatorul 0).
    Lungimea clauzei este aleasă random între 3 și min(10, num_literals).
    """
    clause_size = random.randint(3, min(10, num_literals))
    clause = random.sample(range(1, num_literals + 1), k=clause_size)
    clause = [lit if random.choice([True, False]) else -lit for lit in clause]
    return clause

def generate_random_formula(num_clauses, num_literals, unsat_injection_probability=0.3):
    """
    Generează o formulă CNF ca listă de clauze.
    Opțional, forțează nesatisfiabilitatea prin adăugarea unor clauze unitare contradictorii.
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

# --- Funcții pentru citirea formulărilor din fișier ---

def read_formula_from_file(filename):
    """
    Citește o formulă dintr-un fișier. Se așteaptă ca fiecare linie să conțină o clauză,
    literalile fiind separate prin spațiu, iar clauza terminându-se cu 0.
    Returnează formula ca listă de clauze (lista de liste de int).
    """
    formula = []
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            parts = line.split()
            clause = [int(x) for x in parts]
            if clause and clause[-1] == 0:
                clause.pop()
            formula.append(clause)
    return formula

def read_formulas_from_file(filename):
    """
    Citește mai multe formule dintr-un fișier.
    Se presupune că o formulă este separată de alta printr-o linie goală.
    Returnează o listă de formule.
    """
    formulas = []
    with open(filename, 'r') as f:
        current_formula = []
        for line in f:
            line = line.strip()
            if not line:
                if current_formula:
                    formulas.append(current_formula)
                    current_formula = []
                continue
            parts = line.split()
            clause = [int(x) for x in parts]
            if clause and clause[-1] == 0:
                clause.pop()
            current_formula.append(clause)
        if current_formula:
            formulas.append(current_formula)
    return formulas

# --- Funcție de comparare a solutoarelor SAT ---

def solve_sat_with_all_methods(formula):
    """
    Rulează toate cele trei algoritme (Rezoluție, Davis-Putnam și DPLL) pe formulă.
    Returnează un dicționar cu (rezultat, timp de execuție, memorie consumată în MB, CPU consumat în secunde)
    pentru fiecare algoritm.
    """
    results = {}
    process = psutil.Process(os.getpid())

    # Rezoluție
    gc.collect()
    start_mem = process.memory_info().rss
    start_cpu = process.cpu_times()
    start_time = time.time()
    result_res = resolution_algorithm(formula, max_iterations=3, max_clauses=5000)
    gc.collect()
    elapsed_res = time.time() - start_time
    end_mem = process.memory_info().rss
    end_cpu = process.cpu_times()
    mem_res = (end_mem - start_mem) / (1024 * 1024)  # în MB
    cpu_res = ((end_cpu.user - start_cpu.user) + (end_cpu.system - start_cpu.system))
    results["Rezoluție"] = (result_res, elapsed_res, mem_res, cpu_res)

    # Davis-Putnam
    gc.collect()
    start_mem = process.memory_info().rss
    start_cpu = process.cpu_times()
    start_time = time.time()
    result_dp = davis_putnam(formula)
    gc.collect()
    elapsed_dp = time.time() - start_time
    end_mem = process.memory_info().rss
    end_cpu = process.cpu_times()
    mem_dp = (end_mem - start_mem) / (1024 * 1024)
    cpu_dp = ((end_cpu.user - start_cpu.user) + (end_cpu.system - start_cpu.system))
    results["Davis-Putnam"] = (result_dp, elapsed_dp, mem_dp, cpu_dp)

    # DPLL
    gc.collect()
    start_mem = process.memory_info().rss
    start_cpu = process.cpu_times()
    start_time = time.time()
    result_dpll, _ = dpll_with_timeout(formula, timeout=5)
    gc.collect()
    elapsed_dpll = time.time() - start_time
    end_mem = process.memory_info().rss
    end_cpu = process.cpu_times()
    mem_dpll = (end_mem - start_mem) / (1024 * 1024)
    cpu_dpll = ((end_cpu.user - start_cpu.user) + (end_cpu.system - start_cpu.system))
    results["DPLL"] = (result_dpll, elapsed_dpll, mem_dpll, cpu_dpll)

    return results

# --- Salvarea rezultatelor în fișier ---

def save_results_to_file(filename, formulas):
    """
    Pentru fiecare formulă (fie generată random, fie citită din fișier),
    evaluează rezultatele folosind metodele Rezoluție, Davis-Putnam și DPLL,
    apoi scrie rezultatele într-un fișier.
    """
    with open(filename, 'w') as f:
        for idx, formula in enumerate(formulas, start=1):
            results = solve_sat_with_all_methods(formula)
            f.write(f"Formulă #{idx}: {formula}\n")
            for algo, (result, runtime, mem_usage, cpu_usage) in results.items():
                r_str = 'SAT' if result is True else ('NOT SAT' if result is False else 'TIMEOUT')
                # Afișare memorie în MB și CPU consumption în secunde cu patru zecimale
                f.write(f"{algo}: {r_str}, Timp: {runtime:.4f} secunde, Memorie: {mem_usage:.6f} MB, CPU: {cpu_usage:.6f} sec\n")
            f.write("-" * 50 + "\n")
    print(f"Rezultatele au fost salvate în {filename}")

# --- Funcția principală ---

def main():
    """
    Dacă se furnizează un argument în linia de comandă,
    se citește fișierul (se așteaptă ca acesta să conțină formule în formatul specificat).
    Altfel, se generează formule random.
    Rezultatele se salvează în "sat_results_comparison.txt".
    """
    formulas = []
    if len(sys.argv) > 1:
        input_file = sys.argv[1]
        try:
            formulas = read_formulas_from_file(input_file)
            print(f"S-au încărcat {len(formulas)} formulă(e) din fișierul {input_file}.")
        except Exception as e:
            try:
                formula = read_formula_from_file(input_file)
                formulas.append(formula)
                print(f"S-a încărcat o singură formulă din fișierul {input_file}.")
            except Exception as ex:
                print(f"Eroare la citirea fișierului: {ex}")
                sys.exit(1)
    else:
        num_formulas = 96
        num_clauses = 30
        num_literals = 10
        unsat_prob = 0.3
        formulas = [generate_random_formula(num_clauses, num_literals, unsat_prob)
                    for _ in range(num_formulas)]
    save_results_to_file("sat_results_comparison.txt", formulas)

if __name__ == "__main__":
    main()
