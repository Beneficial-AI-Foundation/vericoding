Vishal Wants to buy 2 gifts for his best friend whose name is Annabelle(her age is 20), So they both went for shopping in a store. But Annabelle gave, Vishal a condition that she will accept this gifts only when the total price of the gifts is the same as her age times 100.
The store contains, a list of items whose prices are also displayed, Now Vishal is asking for your help to buy gifts, as he wants to impress Annabelle this time.
Note: Vishal cannot buy the same item more than once.

-----Input:-----
- The first line of the input contains a single integer $T$. $T$ denoting the number of test cases. The description of $T$ test cases is as follows.
- The next line of the input contains a single integer $N$. $N$ denotes the total number of items in store.
- The next line of the input contains $N$ space-separated integers $A1, A2, A3...An$ where $ith$ number denotes the price of $ith$ element.

-----Output:-----
- For each test-case print "Accepted"(without quotes) if the gifts are accepted by Annabelle, else print "Rejected"(without quotes)

-----Constraints:-----
- $1 \leq T \leq 10^3$
- $1 \leq N \leq 10^5$
- $1 \leq A1, A2, A3...An \leq 10^7$

-----Sample Input:-----
1
5
10 2 1000 50 1000

-----Sample Output:-----
Accepted

-----Explanation:-----
- As the given list of items have 2 items whose price sum up to the age times 100 of Annabelle i.e. 1000+1000 = (20 *100)

def find_gift_pair (n : Nat) (prices : List Nat) : String := sorry
def process_test_cases (numCases : Nat) (cases : List (Nat × List Nat)) : List String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded