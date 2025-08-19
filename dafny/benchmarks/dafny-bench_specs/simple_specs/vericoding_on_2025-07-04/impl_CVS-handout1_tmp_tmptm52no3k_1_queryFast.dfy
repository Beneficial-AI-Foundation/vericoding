//ATOM

//(a)

function sum(a: array<int>, i: int, j: int): int
  reads a
  requires 0 <= i <= j <= a.Length
{
  if (i == j) then 0
  else a[i] + sum(a, i+1, j)
}

//ATOM

//(c)

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  requires a.Length + 1 == c.Length
  requires c[0] == 0
  reads c, a
{
  forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}

//IMPL 

/* code modified by LLM (iteration 4): Fixed sum_equals_prefix lemma with proper inductive proof structure */
lemma sum_equals_prefix(a: array<int>, c: array<int>, end: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires is_prefix_sum_for(a, c)
  requires 0 <= end <= a.Length
  ensures sum(a, 0, end) == c[end]
{
  if end == 0 {
    // Base case: sum(a, 0, 0) == 0 == c[0]
  } else {
    // Inductive case: assume sum(a, 0, end-1) == c[end-1]
    sum_equals_prefix(a, c, end - 1);
    
    // From the definition of sum:
    // sum(a, 0, end) == a[0] + sum(a, 1, end)
    // But we need to relate this to sum(a, 0, end-1)
    
    // Use the fact that sum(a, 0, end) expands as:
    // sum(a, 0, end) == sum(a, 0, end-1) + a[end-1]
    sum_split_at_point(a, 0, end-1, end);
    
    // From is_prefix_sum_for: c[end] == c[end-1] + a[end-1]
    // And from induction: sum(a, 0, end-1) == c[end-1]
    // Therefore: sum(a, 0, end) == c[end-1] + a[end-1] == c[end]
  }
}

/* code modified by LLM (iteration 4): Added helper lemma for single point split */
lemma sum_split_at_point(a: array<int>, start: int, mid: int, end: int)
  requires 0 <= start <= mid < end <= a.Length
  requires mid == end - 1
  ensures sum(a, start, end) == sum(a, start, mid) + a[mid]
{
  // This follows directly from the definition of sum
  // sum(a, start, end) unfolds to sum(a, start, mid) + a[mid] + sum(a, mid+1, end)
  // But since mid+1 == end, sum(a, mid+1, end) == 0
}

/* code modified by LLM (iteration 4): Simplified sum_split_lemma with better inductive structure */
lemma sum_split_lemma(a: array<int>, start: int, mid: int, end: int)
  requires 0 <= start <= mid <= end <= a.Length
  ensures sum(a, start, end) == sum(a, start, mid) + sum(a, mid, end)
{
  if start == mid {
    // Base case: sum(a, start, mid) == 0
  } else if mid == end {
    // Base case: sum(a, mid, end) == 0
  } else {
    // Inductive case: reduce the problem size
    sum_split_lemma(a, start + 1, mid, end);
    
    // We have: sum(a, start + 1, end) == sum(a, start + 1, mid) + sum(a, mid, end)
    // From sum definition:
    // sum(a, start, end) == a[start] + sum(a, start + 1, end)
    // sum(a, start, mid) == a[start] + sum(a, start + 1, mid)
    
    calc {
      sum(a, start, end);
      == a[start] + sum(a, start + 1, end);
      == a[start] + sum(a, start + 1, mid) + sum(a, mid, end);
      == sum(a, start, mid) + sum(a, mid, end);
    }
  }
}

method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires a.Length + 1 == c.Length && c[0] == 0
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c) 
  ensures r == sum(a, i, j)
{
  r := c[j] - c[i];
  
  /* code modified by LLM (iteration 4): Streamlined proof with corrected lemma calls */
  // Establish the key relationships
  sum_equals_prefix(a, c, j);
  sum_equals_prefix(a, c, i);
  sum_split_lemma(a, 0, i, j);
  
  // The proof follows from:
  // c[j] == sum(a, 0, j) (from sum_equals_prefix)
  // c[i] == sum(a, 0, i) (from sum_equals_prefix)  
  // sum(a, 0, j) == sum(a, 0, i) + sum(a, i, j) (from sum_split_lemma)
  // Therefore: sum(a, i, j) == sum(a, 0, j) - sum(a, 0, i) == c[j] - c[i] == r
}