import cpmpy as cp
from nested_explanations import find_explanation_sequence


def jobshop_example() -> cp.Model:

    A1,A2,B1,B2,C1,C2 = cp.intvar(0,20, shape=6, name=("A1","A2","B1","B2","C1","C2"))

    model = cp.Model()

    model += cp.NoOverlap([A1,B1,C1], [3,6,3])
    model += cp.NoOverlap([A2,B2,C2], [3,4,3])

    # precedence constraints
    model += A1 + 3 <= A2
    model += B1 + 6 <= B2
    model += C1 + 3 <= C2

    makespan = cp.intvar(0,15, name="makespan") # optimal makespan is 16
    model += makespan == cp.max(A2+3, B2+6, C2+3)

    return model, ((A1,A2,B1,B2,C1,C2), makespan)

if __name__ == "__main__":

    model, (start, makespan) = jobshop_example()

    print(model)

    assert model.solve() is False
    sequence, proof = find_explanation_sequence(model)
