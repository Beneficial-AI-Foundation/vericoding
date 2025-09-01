function fib4_rec(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 || n == 2 then 0
  else if n == 3 then 1
  else fib4_rec(n - 1) + fib4_rec(n - 2) + fib4_rec(n - 3) + fib4_rec(n - 4)
}

// <vc-helpers>
function fib4_iter(k: nat, cur_minus_3: nat, cur_minus_2: nat, cur_minus_1: nat, cur: nat): nat
  decreases k
  reads this
{
  if k == 0 then cur_minus_3
  else if k == 1 then cur_minus_2
  else if k == 2 then cur_minus_1
  else if k == 3 then cur
  else fib4_iter(k - 1, cur_minus_2, cur_minus_1, cur, cur + cur_minus_1 + cur_minus_2 + cur_minus_3)
}

lemma fib4_iter_equals_fib4_rec(k: nat, cur_minus_3: nat, cur_minus_2: nat, cur_minus_1: nat, cur: nat)
  ensures fib4_iter(k, cur_minus_3, cur_minus_2, cur_minus_1, cur) == fib4_rec(k)
  decreases k
{
  if k == 0 {
    assert fib4_iter(0, _, _, _, _) == cur_minus_3;
    assert fib4_rec(0) == 0;
  } else if k == 1 {
    assert fib4_iter(1, _, _, _, _) == cur_minus_2;
    assert fib4_rec(1) == 0;
  } else if k == 2 {
    assert fib4_iter(2, _, _, _, _) == cur_minus_1;
    assert fib4_rec(2) == 0;
  } else if k == 3 {
    assert fib4_iter(3, _, _, _, _) == cur;
    assert fib4_rec(3) == 1;
  } else {
    fib4_iter_equals_fib4_rec(k - 1, cur_minus_2, cur_minus_1, cur, cur + cur_minus_1 + cur_minus_2 + cur_minus_3);
  }
}
// </vc-helpers>

// <vc-spec>
method fib4(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fib4_rec(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 || n == 2 then {
    result := 0;
  } else if n == 3 then {
    result := 1;
  } else {
    var a: nat := 0;  // Corresponds to fib4_rec(i-3)
    var b: nat := 0;  // Corresponds to fib4_rec(i-2)
    var c: nat := 0;  // Corresponds to fib4_rec(i-1)
    var d: nat := 1;  // Corresponds to fib4_rec(i)

    var i: nat := 3;
    while i < n {
      i := i + 1;
      var next_d: nat := d + c + b + a;
      a := b;
      b := c;
      c := d;
      d := next_d;
    }
    result := d;
  }
}
// </vc-code>

