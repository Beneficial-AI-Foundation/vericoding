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
    var total_sum := count * (n + m) / 2;
    var quotient := total_sum / count;
    var remainder := total_sum % count;
    var rounded := if remainder * 2 < count then quotient
                  else if remainder * 2 > count then quotient + 1
                  else if quotient % 2 == 0 then quotient
                  else quotient + 1;
    result := "0b" + IntToBinary(rounded);
  }
}
// </vc-code>
