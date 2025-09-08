/-
# The Kata
Your task is to transform an input nested list into an hypercube list, which is a special kind of nested list where each level must have the very same size,
This Kata is an exercise on recursion and algorithms. You will need to visualize many aspects of this question to be able to solve it efficiently, as such there is a section on definitions of the terms that will be used in the Kata, make sure to fully understand them before attempting. A naive brute-force-ish answer will most likely fail the tests. There will be tests on  nested lists of dimension and size up to 10. Good luck.

# Definitions
### Nested List
A nested list is a list that may contain either non-list items or more nested lists as items in the list. Here are a few examples of nested lists.

    [[2, 3], 4, 5, 6, [2, [2, 3, 4, 5], 2, 1, 2], [[[[1]]]], []]
    [[[]]]
    [1, 2]
    [[], []]
    [4, 5, 6, 7, [], 2]
    []

- A *basic element* refers to any non-list element of a nested list.

- A nested list's *dimension* is defined as the deepest the list goes.  

- A nested list's *size* is defined as the longest the list or any of its sublists go.  

For example, the *dimension* and *size* of the above nested lists is as follows.

    [[2, 3], 4, 5, 6, [2, [2, 3, 4, 5], 2, 1, 2], [[[[1]]]], []]  # dimension: 5, size: 7
    [[[]]]                                                        # dimension: 3, size: 1
    [1, 2]                                                        # dimension: 1, size: 2
    [[], []]                                                      # dimension: 2, size: 2
    [4, 5, 6, 7, [], 2]                                           # dimension: 2, size: 6
    []                                                            # dimension: 1, size: 0

### Hypercube List
- A `1`-dimensional **hypercube list** of size `n` is a nested list of dimension `1` and size `n`.  

- A `d`-dimensional hypercube list of size `n` is a nested list of dimension `d` and size `n` such that the nested list has `n` elements each of which is a `d - 1`-dimensional hypercube list of size `n`.  

Here are some examples of hypercube lists.

    [1]                                                       # dimension: 1, size: 1
    [[1, 2], [3, 4]]                                          # dimension: 2, size: 2
    [[1, 2, 3], [4, 5, 6], [7, 8, 9]]                         # dimension: 2, size: 3
    [[0]]                                                     # dimension: 2, size: 1
    [[[0, 0], [1, 1]], [[2, 2], [3, 3]]]                      # dimension: 3, size: 2
    [1, 2, 3, 4]                                              # dimension: 1, size: 4
    [[1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4]]  # dimension: 2, size: 4

# The Task
Your task is to implement `normalize` which converts any given `nested_list` to be in hypercube format with the same dimension and size as the given nested list, extending and growing with the given `growing_value`. The default growing value is the integer `0`.

### The Algorithm
In most scenarios you will encounter a nested list that does not have the same size throughout. When working on such a list the algorithm should behave as follows.

 * If a hypercube list of dimension 1 needs extra elements, append the required number of growing value elements.
 * If a hypercube list of dimension greater than 1 has a direct basic element as a child, replace it with the required hypercube list with its basic elements all being the replaced item.
 * If a hypercube list of dimension greater than 1 needs extra elements, append the required hypercube list with its basic elements all being the growing value.

Take note of the given example, it will be very helpful in understanding the intricacies of the algorithm.

    >>> normalize(
            [
                [
                    [2, 3, 4],
                    [1, 2],
                    2,
                    [1]
                ],
                [
                    2,
                    [2, 3],
                    1,
                    4,
                    [2, 2, 6, 7]
                ],
                5
            ]
        )

Gives the following result.

    [
        [
            [2, 3, 4, 0, 0],
            [1, 2, 0, 0, 0],
            [2, 2, 2, 2, 2],
            [1, 0, 0, 0, 0],
            [0, 0, 0, 0, 0]
        ],
        [
            [2, 2, 2, 2, 2],
            [2, 3, 0, 0, 0],
            [1, 1, 1, 1, 1],
            [4, 4, 4, 4, 4],
            [2, 2, 6, 7, 0]
        ],
        [
            [5, 5, 5, 5, 5],
            [5, 5, 5, 5, 5],
            [5, 5, 5, 5, 5],
            [5, 5, 5, 5, 5],
            [5, 5, 5, 5, 5]
        ],
        [
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0]
        ],
        [
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0],
            [0, 0, 0, 0, 0]
        ]
    ]

Good luck!
-/

-- <vc-helpers>
-- </vc-helpers>

def normalize {α : Type} (lst : List (List α ⊕ α)) : List (List α ⊕ α) := sorry

theorem normalize_identity_flat {α : Type} (lst : List α) :
  normalize (lst.map (fun x => Sum.inr x)) = lst.map (fun x => Sum.inr x) := sorry

theorem normalize_sublist_lengths {α : Type} (lst : List (List α ⊕ α)) :
  (∃ x y, x ∈ lst ∧ y ∈ lst ∧ ∃ l1 l2, x = Sum.inl l1 ∧ y = Sum.inl l2) →
  (∀ x y, x ∈ normalize lst → y ∈ normalize lst → 
    match x, y with 
    | Sum.inl l1, Sum.inl l2 => List.length l1 = List.length l2
    | _, _ => True) := sorry

theorem normalize_empty {α : Type} :
  normalize ([] : List (List α ⊕ α)) = [] := sorry

theorem normalize_singleton_empty {α : Type} :
  normalize [Sum.inl ([] : List α)] = [Sum.inl []] := sorry

-- Apps difficulty: interview
-- Assurance level: guarded