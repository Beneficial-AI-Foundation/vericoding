/-
-----
__CLEAR CUTTER'S NEEDS YOUR HELP!__
-----

The logging company Clear Cutter's makes its money by optimizing the price-to-length of each log they cut before selling them. An example of one of their price tables is included:

```python
# So a price table p
p = [ 0,  1,  5,  8,  9, 10]

# Can be imagined as:
# length i | 0  1  2  3  4  5 *in feet*
# price pi | 0  1  5  8  9 10 *in money*
```

They hired an intern last summer to create a recursive function for them to easily calculate the most profitable price for a log of length _n_ using price table _p_ as follows:

```python
def cut_log(p, n):
   if (n == 0):
      return 0
   q = -1
   for i in range(1, n+1)
      q = max(q, p[i] + cut_log(p, n-i))
   return q
```

An example of the working code:
```python
cut_log(p, 5) # => 13
# 5ft = $10, BUT 2ft + 3ft = 5ft -> $5 + $8 = $13 which is greater in value
```

However, their senior software engineer realized that the number of recursive calls in the function gives it an awful running time of 2^n (as this function iterates through ALL 2^n-1 possibilities for a log of length n).

Having discovered this problem just as you've arrived for your internship, he responsibly delegates the issue to you.

Using the power of Stack Overflow and Google, he wants you to create a solution that runs in Θ(n^2) time so that it doesn't take 5 hours to calculate the optimal price for a log of size 50. (He also suggests to research the problem using the keywords in the tags)

__(Be aware that if your algorithm is not efficient, it will attempt to look at 2^49 = 562949953421312 nodes instead of 49^2 = 2401... The solution will automatically fail if it takes longer than 6 seconds... which occurs at right around Log 23)__
-/

-- <vc-helpers>
-- </vc-helpers>

def cut_log (prices : List Nat) (n : Nat) : Nat := sorry

theorem cut_log_non_negative (prices : List Nat) (n : Nat) :
  cut_log prices n ≥ 0 := sorry

theorem cut_log_monotonic (prices : List Nat) (n : Nat) :
  n > 0 → cut_log prices n ≥ cut_log prices (n-1) := sorry

theorem cut_log_zero (prices : List Nat) :
  cut_log prices 0 = 0 := sorry

theorem cut_log_single_unit (prices : List Nat) :
  prices ≠ [] → prices.length > 1 → cut_log prices 1 = prices[1]! := sorry

/-
info: 13
-/
-- #guard_msgs in
-- #eval cut_log [0, 1, 5, 8, 9, 10] 5

/-
info: 22
-/
-- #guard_msgs in
-- #eval cut_log [0, 1, 5, 8, 9, 10, 17, 17, 20] 8

/-
info: 12
-/
-- #guard_msgs in
-- #eval cut_log [0, 3, 5, 8, 9, 10, 17, 17, 20] 4

-- Apps difficulty: interview
-- Assurance level: unguarded