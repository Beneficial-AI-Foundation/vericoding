ghost function f(n: int): int {
  if n <= 0 then 1 else n + f(n-1)*f(n-2)
}

ghost function fSum(n: nat): int {
 // give the body of this function
  // it should return Sum(i: 0<=i < n: f(i))
  if n <= 0 then 0 else f(n-1) + fSum(n-1)
}

// <vc-helpers>
function computeF(n: int): int {
  if n <= 0 then 1 
  else if n == 1 then 2
  else 
    var f_prev2 := 1; // f(0);
    var f_prev1 := 2; // f(1);
    var j := 2;
    computeFHelper(n, j, f_prev2, f_prev1)
}

function computeFHelper(target: int, j: int, f_prev2: int, f_prev1: int): int
  requires j >= 2
  requires target >= j - 1
  decreases target - j + 1
{
  if j > target then f_prev1
  else 
    var f_curr := j + f_prev1 * f_prev2;
    computeFHelper(target, j + 1, f_prev1, f_curr)
}

lemma computeFCorrect(n: int)
  ensures computeF(n) == f(n)
{
  if n <= 0 {
    // Base case
  } else if n == 1 {
    // f(1) = 1 + f(0) * f(-1) = 1 + 1 * 1 = 2
  } else {
    // Need to prove the helper function is correct
    computeFHelperCorrect(n, 2, 1, 2);
  }
}

lemma computeFHelperCorrect(target: int, j: int, f_prev2: int, f_prev1: int)
  requires j >= 2
  requires target >= j - 1
  requires f_prev2 == f(j-2)
  requires f_prev1 == f(j-1)
  ensures computeFHelper(target, j, f_prev2, f_prev1) == f(target)
  decreases target - j + 1
{
  if j > target {
    // f_prev1 == f(j-1) == f(target)
  } else {
    var f_curr := j + f_prev1 * f_prev2;
    // f_curr == j + f(j-1) * f(j-2) == f(j)
    computeFHelperCorrect(target, j + 1, f_prev1, f_curr);
  }
}
// </vc-helpers>

// <vc-spec>
method problem6(n:nat) returns (a: int)
ensures a == fSum(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    a := 0;
    return;
  }
  
  a := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant a == fSum(i)
  {
    // Compute f(i)
    var fi: int;
    fi := computeF(i);
    computeFCorrect(i);
    
    a := a + fi;
    i := i + 1;
  }
}
// </vc-code>