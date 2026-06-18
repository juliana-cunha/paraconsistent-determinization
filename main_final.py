"""
Determinization of a Finite Paraconsistent Non-Deterministic Automaton (FPNA)

This script implements the determinization method for FPNA whose transitions
are taken from the unit square [0,1]^2. It includes examples from Section 3
and prints the resulting deterministic automaton (FPDA).
"""

# -------------------------------
# Define a Paraconsistent Automaton (Example 1)
# -------------------------------

Sigma = ['a', 'b']          # input alphabet
Q = {0, 1, 2, 3}            # set of states
initial = 0                 # initial state
F = [0, 3]                  # final states

# Transition function: 
# Note that \varepsilon-transitions are marked by symbol 'e'.
delta = {
    (0, 'b', 0): (1, 0),
    (0, 'a', 1): (0.5, 0.6),
    (0, 'a', 2): (0.4, 0.8),
    (2, 'b', 0): (1, 0),
    (1, 'b', 3): (0.8, 1)
}


# Other examples (uncomment to test):
'''
# Example 5
Sigma = ['a', 'b']
Q = {0, 1, 2}
initial = 0
F = [2]
delta = {
    (0, 'a', 0): (1, 0),
    (0, 'b', 0): (1, 1),
    (0, 'a', 1): (0.5, 0.6),
    (0, 'e', 1): (1, 0),
    (1, 'b', 2): (0.8, 1)
}
'''

'''
#Extra Example
Sigma = ['a', 'b']
Q = {0, 1, 2, 3}
initial = 0
F = [2]
delta = {
    (0, 'e', 1): (1, 0),
    (1, 'a', 2): (1, 0.2),
    (2, 'e', 3): (1, 0),
    (3, 'b', 3): (0.5, 0.5),
    (3, 'e', 1): (1, 0),
    (3, 'e', 0): (1,0)
}
'''


# -------------------------------
# Complete transition function
# -------------------------------

def complete():
    """
    Ensures delta is total by adding (0,1) where transitions are missing.
    """
    for q1 in Q:
        for q2 in Q:
            for a in Sigma:
                if (q1, a, q2) not in delta:
                    delta[(q1, a, q2)] = (0, 1)
    return delta


delta = complete()


# -------------------------------
# Algebraic operators in [0,1]^2
# -------------------------------

def TwistAnd(pair1,pair2):
    return (min(pair1[0],pair2[0]),max(pair1[1],pair2[1]))

def TwistOr(pair1,pair2):
    return (max(pair1[0],pair2[0]),min(pair1[1],pair2[1]))


# -------------------------------
# \varepsilon-closure
# -------------------------------

def epsilonclosure(p):
    """
    Computes the \varepsilon-closure of state p.
    \varepsilon-transitions are marked by symbol 'e'.
    """
    closure = {p}
    stack = [p]

    while stack:
        q = stack.pop()

        for r in Q:
            if (q, 'e', r) in delta and r not in closure:
                closure.add(r)
                stack.append(r)

    return closure


def dict_closure():
    """Computes the \varepsilon-closure of all states"""
    return {q: epsilonclosure(q) for q in Q}

all_closures = dict_closure()


def dict_inverse_closure():
    """
    Returns a dictionary mapping each state p to its \varepsilon-closure^{-1}   
    """
    inv_closures = {p: set() for p in Q}

    for q, closure in all_closures.items():
        for p in closure:
            inv_closures[p].add(q)

    return inv_closures


all_closures_inv = dict_inverse_closure()


# -------------------------------
# Extended transition function
# -------------------------------


from functools import lru_cache

@lru_cache(maxsize=None)

def deltastar(q1, w, q2):
    """
    Computes the pair of truth values associated with executing
    word w from q1 to q2.
    """

    result = (0, 1)

    # Base case
    if w == '':
        return (1, 0) if q2 in all_closures[q1] else (0, 1)

    # Inductive step
    for p in Q:
        for r in all_closures_inv[q2]:

            step_val = deltastar(q1, w[:-1], p)
            next_val = delta[(p, w[-1], r)]

            aux = TwistAnd(step_val, next_val)
            result = TwistOr(result, aux)

    return result

# -------------------------------
# Language of the PNFA
# -------------------------------

def lang(w):
    """
    Returns the pair of truth values associated with
    the acceptance of w by the PNFA.
    """
    
    acceptance = (0, 1)

    for qf in F:
        acceptance = TwistOr(acceptance,deltastar(initial, w, qf)
        )

    return acceptance


# -------------------------------
# Reachability
# -------------------------------

def reach(p, w):
    '''
    Given a state p and a word w
    the function returns all states that starting from p and executing w
    one can reach without collapsing to (0,1)
    '''
    result = set()

    for q in Q:
        if deltastar(p, w, q) != (0, 1):
            result.add(q)

    return result


# -------------------------------
# Auxiliary functions
# -------------------------------

def add_letter(W):
    """Extend each word in W by one letter."""
    return [w + a for w in W for a in Sigma]


def to_state(S):
    """Encode a set of states as a string. E.g. {1,2,3} -> '123' """
    return ''.join(map(str, sorted(S)))


def is_final(QD):
    """Return final states of the determinized automaton"""
    return {
        S for S in QD
        if any(int(q) in F for q in S)
    }


# -------------------------------
# Determinization Step 1
# -------------------------------

def step1():
    """
    Computes the unweighted transitions of the determinized version of the automaton.
    """

    # Initial state of the determinized automaton
    initial_state = to_state(all_closures[initial])

    # Stores state reached after reading each word
    words_states = {}

    # Stores transitions of the determinized automaton
    transitions = set()

    # Words to be explored from the initial state
    next_words = Sigma.copy()

    while next_words:

        words = next_words.copy()

        for w in next_words:

            prev_word = w[:-1]

            if prev_word in words_states:
                # State reached after executing the prefix w[:-1]
                prev_state = words_states[prev_word]
            else:
                # If prev_word == '', the prev_state is the epsilonclosure(initial)
                prev_state = initial_state

            # State reached after executing the full word w
            new_state = to_state(reach(initial, w))

            # Add transition if it is non-empty and not already known
            if new_state != '' and (prev_state, w[-1], new_state) not in transitions:
                transitions.add((prev_state, w[-1], new_state))

            # Remove word from next iteration if it leads to a deadlock, or a state already discovered before
            if new_state == '' or new_state in words_states.values():
                words.remove(w)

            # Store the state reached by executing w
            words_states[w] = new_state

        # Compute the next set of words to be explored
        next_words = add_letter(words)

    return transitions



# -------------------------------
# Determinization Step 2
# -------------------------------

def step2(transitions):
    """
    Assign weights to transitions from Step 1 and compute QD and FD
    """

    # States
    QD = set()

    # Initial state
    initial_state = to_state(all_closures[initial])
    QD.add(initial_state)

    # Weighted transition function
    deltaD = {}

    for (S1, a, S2) in transitions:

        QD.add(S1)
        QD.add(S2)

        value = (0, 1)

        for p in S1:
            for q in S2:
                value = TwistOr(
                    value,
                    delta[(int(p), a, int(q))]
                )

        deltaD[(S1, a, S2)] = value

    # Final states
    FD = {
        S for S in QD
        if any(int(q) in F for q in S)
    }

    return {
        "Q": QD,
        "initial": initial_state,
        "F": FD,
        "delta": deltaD
    }


# -------------------------------
# Full process
# -------------------------------

def determinization():
    print("Constructing FPDA determinization...\n")

    fpda = step2(step1())

    print("States:", fpda["Q"])
    print("Initial state:", fpda["initial"])
    print("Final states:", fpda["F"])

    print("Transitions:")
    for t, v in fpda["delta"].items():
        print(" ",t, "->", v)

    return fpda

# -------------------------------
# Run
# -------------------------------

if __name__ == "__main__":
    Det=determinization()


