function CountOnesInBinary(n: int): int
    requires n >= 1
    ensures CountOnesInBinary(n) >= 1
    decreases n
{
    if n == 1 then 1
    else if n % 2 == 1 then 1 + CountOnesInBinary(n / 2)
    else CountOnesInBinary(n / 2)
}

predicate ValidInput(x: int) {
    x >= 1
}

predicate ValidOutput(x: int, result: int) {
    ValidInput(x) && result == CountOnesInBinary(x)
}

// <vc-helpers>
function CountOnes(n: int): int
{
    if n <= 0 then 0 else CountOnesInBinary(n)
}

lemma CountOnesRecursiveProperty(n: int)
    requires n >= 1
    ensures CountOnesInBinary(n) == (if n % 2 == 1 then 1 else 0) + CountOnes(n / 2)
{
    // This lemma is provable by unfolding the definitions of CountOnes and CountOnesInBinary.
    // An empty body is sufficient for Dafny to prove it automatically.
}
// </vc-helpers>

// <vc-spec>
method MinBacteria(x: int) returns (result: int)
    requires ValidInput(x)
    ensures ValidOutput(x, result)
// </vc-spec>
// <vc-code>
{
  var count: int := 0;
  var current_x: int := x;

  while current_x > 0
    invariant current_x >= 0
    invariant CountOnesInBinary(x) == count + CountOnes(current_x)
    decreases current_x
  {
    // The lemma below helps Dafny relate the recursive definition to the iterative step.
    CountOnesRecursiveProperty(current_x);

    if current_x % 2 == 1 {
      count := count + 1;
    }
    current_x := current_x / 2;
  }
  
  result := count;
}
// </vc-code>

