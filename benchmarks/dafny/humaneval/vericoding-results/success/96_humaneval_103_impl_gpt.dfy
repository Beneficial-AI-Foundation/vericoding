// <vc-preamble>

function IntToBinary(n: nat): string
{
    if n == 0 then "0"
    else IntToBinaryHelper(n)
}

function IntToBinaryHelper(n: nat): string
    requires n > 0
{
    if n == 1 then "1" 
    else IntToBinaryHelper(n / 2) + (if n % 2 == 1 then "1" else "0")
}
// </vc-preamble>

// <vc-helpers>
lemma IntToBinaryHelper_LenAtLeast1(n: nat)
  requires n > 0
  ensures |IntToBinaryHelper(n)| >= 1
  decreases n
{
  if n == 1 {
    // length("1") = 1
  } else {
    assert n >= 2;
    assert n / 2 >= 1;
    IntToBinaryHelper_LenAtLeast1(n / 2);
    if n % 2 == 1 {
      assert |IntToBinaryHelper(n / 2) + "1"| == |IntToBinaryHelper(n / 2)| + |"1"|;
    } else {
      assert |IntToBinaryHelper(n / 2) + "0"| == |IntToBinaryHelper(n / 2)| + |"0"|;
    }
  }
}

lemma IntToBinary_LenAtLeast1(n: nat)
  ensures |IntToBinary(n)| >= 1
{
  if n == 0 {
    // length("0") = 1
  } else {
    IntToBinaryHelper_LenAtLeast1(n);
  }
}
// </vc-helpers>

// <vc-spec>
method rounded_avg(n: int, m: int) returns (result: string)
    requires n > 0 && m > 0
    ensures n > m ==> result == "-1"
    ensures n <= m ==> |result| >= 3 && result[0..2] == "0b"
    ensures n <= m ==> (
        var count := m - n + 1;
        var total_sum := count * (n + m) / 2;
        var quotient := total_sum / count;
        var remainder := total_sum % count;
        var rounded := if remainder * 2 < count then quotient
                      else if remainder * 2 > count then quotient + 1
                      else if quotient % 2 == 0 then quotient
                      else quotient + 1;
        result == "0b" + IntToBinary(rounded)
    )
// </vc-spec>
// <vc-code>
{
  if n > m {
    result := "-1";
  } else {
    var count := m - n + 1;
    assert count >= 1;
    var total_sum := count * (n + m) / 2;
    var quotient := total_sum / count;
    var remainder := total_sum % count;

    var rounded: int;
    if remainder * 2 < count {
      rounded := quotient;
    } else if remainder * 2 > count {
      rounded := quotient + 1;
    } else {
      if quotient % 2 == 0 {
        rounded := quotient;
      } else {
        rounded := quotient + 1;
      }
    }

    assert rounded >= 0;
    var bin := IntToBinary(rounded as nat);
    IntToBinary_LenAtLeast1(rounded as nat);
    result := "0b" + bin;
    assert |result| >= 3;
    assert result[0..2] == "0b";
  }
}
// </vc-code>
