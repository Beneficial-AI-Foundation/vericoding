

// <vc-helpers>
predicate isEven(n: int)
  ensures isEven(n) <==> n % 2 == 0
{
  n % 2 == 0
}

function findMaxEven(x: int, y: int): (r: int)
  requires 0 <= x <= y
  ensures r % 2 == 0
  ensures x <= r <= y
  ensures forall i : int :: x <= i <= y && isEven(i) ==> r >= i
{
  if y % 2 == 0 then y else 
    if y - 1 >= x then y - 1 else x
}

lemma findMaxEvenLemma(x: int, y: int)
  requires 0 <= x <= y
  ensures findMaxEven(x, y) % 2 == 0
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method choose_num(x : int, y : int) returns (num : int)
  // pre-conditions-start
  requires 0 <= x && 0 <= y
  // pre-conditions-end
  // post-conditions-start
  ensures num == -1 || (num >= x && num <= y)
  ensures num == -1 || num % 2 == 0
  ensures num == -1 || (forall i : int :: x <= i <= y && i % 2 == 0 ==> num >= i)
  ensures num == -1 <==> x >= y
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if x > y {
    num := -1;
  } else {
    num := findMaxEven(x, y);
    if num % 2 != 0 {
      num := -1;
    }
  }
}
// </vc-code>

