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
