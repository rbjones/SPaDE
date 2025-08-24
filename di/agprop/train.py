# train.py
# Template for training/testing the propositional logic environment

from proplogic import PropositionalLogicEnv

def main():
    axioms = ["A", "A=>B"]
    goal = "B"
    env = PropositionalLogicEnv(axioms, goal)
    print("Initial board:", env.getInitBoard())
    # Add training or testing code here

if __name__ == "__main__":
    main()
