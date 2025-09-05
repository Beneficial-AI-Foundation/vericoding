Chef loves saving money and he trusts none other bank than State Bank of Chefland. Unsurprisingly, the employees like giving a hard time to their customers. But instead of asking them to stand them in long queues, they have weird way of accepting money.
Chef did his homework and found that the bank only accepts the money in coins such that the sum of the denomination with any previously deposited coin OR itself can't be obtained by summing any two coins OR double of any coin deposited before. Considering it all, he decided to start with $1$ Chefland rupee and he would keep choosing smallest possible denominations upto $N$ coins. Since chef is busy with his cooking, can you find out the $N$ denomination of coins chef would have to take to the bank? Also find the total sum of money of those $N$ coins.

-----Input:-----
- First line has a single integer $T$ i.e. number of testcases.
- $T$ lines followed, would have a single integer $N$ i.e. the number of coins the chef is taking.

-----Output:-----
- Output for $i$-th testcase ($1 ≤ i ≤ T$) would have 2 lines.
- First line would contain $N$ integers i.e. the denomination of coins chef would deposit to the bank.
- Second line would contain a single integer i.e. the sum of all the coins chef would deposit.

-----Constraints:-----
- $1 ≤ T ≤ 700$
- $1 ≤ N ≤ 700$

-----Subtasks:-----
- $20$ points: $1 ≤ T, N ≤ 80$
- $70$ points: $1 ≤ T, N ≤ 500$
- $10$ points: $1 ≤ T, N ≤ 700$ 

-----Sample Input:-----
4
1
2
3
4

-----Sample Output:-----
1
1
1 2
3
1 2 4
7
1 2 4 8
15

-----Explanation:-----
For testcase 1: First coin is stated to be 1, hence for $N$ = 1, 1 is the answer.
For testcase 2: Since chef chooses the lowest possible denomination for each $i$-th coin upto $N$ coins, second coin would be 2. Only sum possible with N = 1 would be 1+1 = 2. For N = 2, $\{1+2,  2+2\}$ $\neq$ $2$.
For testcase 3: With first two coins being 1 and 2, next coin couldn't be 3 because 3+1 = 2+2, but $\{4+1,  4+2,  4+4\}$ $\neq$ $\{1+1,  1+2,  2+2\}$

def get_coins_and_sum (n: Nat) : List Nat × Nat :=
  sorry

def list_is_sorted {α: Type} (l: List α) (less_eq : α → α → Prop) : Prop :=
  ∀ i j, i < j → j < l.length → less_eq (l.get ⟨i, sorry⟩) (l.get ⟨j, sorry⟩)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
