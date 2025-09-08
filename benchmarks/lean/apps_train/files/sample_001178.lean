/-
Lets wish Horsbug98 on his birthday and jump right into the question.
In Chefland, $6$ new mobile brands have appeared each providing a range of smartphones. For simplicity let the brands be represented by numbers $1$ to $6$. All phones are sold at the superstore. 
There are total $N$ smartphones. Let $P_i$ & $B_i$ be the price and the brand of the $i^{th}$ smartphone. The superstore knows all the price and brand details beforehand. 
Each customer has a preference for brands. The preference is a subset of the brands available (i.e $1$ to $6$). Also, the customer will buy the $K^{th}$ costliest phone among all the phones of his preference.
You will be asked $Q$ queries. Each query consists of the preference of the customer and $K$.
Find the price the customer has to pay for his preference. If no such phone is available, print $-1$
Note that for each query the total number of smartphones is always $N$ since, after each purchase, the phones are replaced instantly.

-----Input:-----
- First Line contains $N$ and $Q$
- Second-line contains $N$ integers $P_1,P_2,...,P_N$ (Price)
- Third line contains $N$ integers $B_1,B_2,...,B_N$ (Brand)
- Each of the next Q lines contains a query, the query is describes below
- First line of each quey contains $b$ and $K$ where $b$ is the size of the preference subset.
- Second line of each query contains $b$ integers, describing the preference subset.

-----Output:-----
For each query, print the price to be paid.

-----Constraints-----
- $1 \leq N, Q, P_i \leq 10^5$
- $1 \leq B_i, b \leq 6$
- $1 \leq K \leq N$

-----Sample Input:-----
4 2
4 5 6 7 
1 2 3 4 
3 3
1 2 3
3 4
4 5 6 

-----Sample Output:-----
4

-1

-----Explaination-----
Query 1: The preference subset is {1, 2, 3}, The prices of phones available of these brands are {4, 5, 6}. The third costliest phone is 4.
Query 2: The preference subset is {4, 5, 6}, The prices of phones available of these brands are {7}.
Fouth costliest phone is required, which is not available. Hence, answer is $-1$.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_phones (N Q : Nat) (prices : List Nat) (brands : List Nat) 
  (queries : List ((Nat × Nat) × List Nat)) : List Int := sorry

theorem solve_phones_result_length (N Q : Nat) (prices : List Nat) 
  (brands : List Nat) (queries : List ((Nat × Nat) × List Nat)) :
  let result := solve_phones N Q prices brands queries
  List.length result = Q := sorry

theorem solve_phones_result_valid (N Q : Nat) (prices : List Nat) 
  (brands : List Nat) (queries : List ((Nat × Nat) × List Nat)) : 
  let result := solve_phones N Q prices brands queries
  ∀ x ∈ result, x = -1 ∨ (∃ p ∈ prices, x = p) := sorry

theorem solve_phones_invalid_k (N : Nat) (prices : List Nat)
  (brands : List Nat) (preferred_brands : List Nat) :
  let k := List.length prices + 1
  let query := ((List.length preferred_brands, k), preferred_brands)
  let result := solve_phones N 1 prices brands [query]
  result = [-1] := sorry

-- Apps difficulty: interview
-- Assurance level: guarded