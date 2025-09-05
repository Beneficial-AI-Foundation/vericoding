Imagine the following situations:

- A truck loading cargo
- A shopper on a budget
- A thief stealing from a house using a large bag
- A child eating candy very quickly

All of these are examples of ***The Knapsack Problem***, where there are more things that you ***want*** to take with you than you ***can*** take with you.

The Problem
===

Given a container with a certain capacity and an assortment of discrete items with various sizes and values (and an infinite supply of each item), determine the combination of items that fits within the container and maximizes the value of the collection.

However, **DO NOT** attempt to solve the problem **EXACTLY!** (we will do that in Part 2)

The Simplification
===

Because the optimal collection of items is **MUCH** more difficult to determine than a nearly-optimal collection, this kata will only focus on one specific nearly-optimal solution: the greedy solution. The greedy solution is that which always adds an item to the collection if it has the highest value-to-size ratio.

For example, if a "greedy thief" with a 10-Liter knapsack sees two types of items

- a 6-Liter item worth $9 (1.5 $/L)

- a 5-Liter item worth $5 (1.0 $/L)

the thief will take 1 of the 6-Liter items instead of 2 of the 5-Liter items. Although this means the thief will only profit $9 instead of $10, the decision algorithm is much simpler. Maybe the thief is bad at math.

Now, go be bad at math!

The Kata
===

Write the function `knapsack` that takes two parameters, `capacity` and `items`, and returns a list of quantities.

`capacity` will be a positive number

`items` will be an array of arrays of positive numbers that gives the items' sizes and values in the form [[size 1, value 1], [size 2, value 2], ...]

`knapsack` will return an array of integers that specifies the quantity of each item to take according to the greedy solution (the order of the quantities must match the order of `items`)

def knapsack (capacity : Nat) (items : List (Nat × Nat)) : List Nat :=
  sorry

def sumList (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => h + sumList t

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
