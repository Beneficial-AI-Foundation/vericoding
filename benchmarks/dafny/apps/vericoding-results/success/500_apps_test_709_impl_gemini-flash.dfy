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
function NumBits(n: int): nat
  requires n >= 1
  decreases n
{
  if n == 1 then 1
  else 1 + NumBits(n / 2)
}

lemma lemma_CountOnesZero(n: int)
  requires n >= 1
  ensures CountOnesInBinary(n) > 0
{
  if n == 1 {
  } else if n % 2 == 1 {
    lemma_CountOnesZero(n / 2);
  } else {
    lemma_CountOnesZero(n / 2);
  }
}

lemma lemma_CountOnesBounded(n: int)
  requires n >= 1
  ensures CountOnesInBinary(n) <= NumBits(n)
  decreases n
{
  if n == 1 {
  } else if n % 2 == 1 {
    lemma_CountOnesBounded(n / 2);
  } else {
    lemma_CountOnesBounded(n / 2);
  }
}
// </vc-helpers>

// <vc-spec>
method MinBacteria(x: int) returns (result: int)
    requires ValidInput(x)
    ensures ValidOutput(x, result)
// </vc-spec>
// <vc-code>
{
  lemma_CountOnesZero(x);
  if x == 1 {
    result := 1;
  } else if x % 2 == 1 {
    var rec_result := MinBacteria(x / 2);
    result := 1 + rec_result;
  } else {
    var rec_result := MinBacteria(x / 2);
    result := rec_result;
  }
}
// </vc-code>

