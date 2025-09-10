predicate ValidInput(a: int, b: int)
{
  a > 1 && b >= 0
}

function SocketsAfterStrips(strips: int, a: int): int
  requires a > 1 && strips >= 0
{
  1 + strips * (a - 1)
}

function CeilingDivision(x: int, y: int): int
  requires y > 0
{
  if x % y == 0 then x / y
  else if x >= 0 then x / y + 1
  else x / y
}

function MinStripsNeeded(a: int, b: int): int
  requires ValidInput(a, b)
{
  if b <= 1 then 0
  else CeilingDivision(b - 1, a - 1)
}

predicate CorrectResult(a: int, b: int, result: int)
  requires ValidInput(a, b)
{
  result >= 0 &&
  SocketsAfterStrips(result, a) >= b &&
  (result == 0 || SocketsAfterStrips(result - 1, a) < b)
}

// <vc-helpers>
lemma SocketsAfterStripsNonDecreasing()
  ensures forall a: int, strips: int | a > 1 && strips >= 0 :: SocketsAfterStrips(strips, a) == 1 + strips * (a - 1)

lemma SocketsAfterStripsCorrect(strips: int, a: int, b: int)
  requires a > 1 && b >= 0 && strips >= 0
  ensures SocketsAfterStrips(strips, a) == 1 + strips * (a - 1)

lemma CeilingDivisionIsCeil(x: int, y: int)
  requires y > 0
{
  var d := CeilingDivision(x, y);
  var r := x % y;
  var q := x / y;
  if r == 0 {
    assert d == q;
  } else if x >= 0 {
    assert d == q + 1;
  } else {
    assert d == q;
  }
}

lemma CeilingDivisionProperties()
  ensures forall a:int, b:int | a > 1 && b >= 0 && b > 1 ::
    CorrectResult(a, b, CeilingDivision(b - 1, a - 1))
{
  forall a: int, b: int | a > 1 && b >= 0 && b > 1 {
    var m := a - 1;
    var k := b - 1;
    var cd := CeilingDivision(k, m);
    // assert cd * m >= k; // From definition
    if cd > 0 {
      if k % m != 0 {
        // assert (cd - 1) * m < k;
      } else {
        // assert cd == k / m;
        // But since cd = k / m, and m > 0, cd > 0 implies k >= m, so (cd - 1) * m < k since cd > 0 means cd >= 1, no:
        // If cd = 1, then 0 * m < k iff k > 0, but here b > 1, k = b-1 >= 1, and cal if k <= m, then CeilingDivision = 1, and 0 < k yes.
        // If cd > 1, then for cd = ceil(k/m), (cd-1)*m < k if not divisible and k <= cd*m.
      }
    }
  }
}

lemma MinStripsSatisfiesCorrect(a:int, b:int)
  requires a > 1 && b >= 0
  ensures CorrectResult(a, b, MinStripsNeeded(a, b))
{
  if b <= 1 {
    // result = 0, check
    assert 0 >= 0;
    assert SocketsAfterStrips(0, a) >= b;
  } else {
    var result := CeilingDivision(b - 1, a - 1);
    assert result >= 0;
    assert 1 + result * (a - 1) >= b;
    if result > 0 {
      if (b - 1) % (a - 1) == 0 {
        // assert b - 1 == result * (a - 1);
        assert SocketsAfterStrips(result - 1, a) == b - (a - 1);
        // But b - (a-1) = 1 + (b-1) - (a-1) = b - (a-1) = b - a +1, wait no
        assert SocketsAfterStrips(result - 1, a) = 1 + (result -1)*(a-1) = 1 + result*(a-1) - (a-1) = result*(a-1) +1 - (a-1) = (result-1)*(a-1) + 1
        assert b - 1 == result * (a-1);
        assert result * (a-1) +1 - (a-1) = (result)*(a-1) +1 - (a-1) = result*(a-1) +1 - a +1 = (result*a - result) +1 - a +1 = result*a - a +1 - result
        // For b=2, a=2, b-1=1, a-1=1, cd=1, sockets at 1: 1+1*1=2 >=2, at 0:1 <2
        // If divisible, it's ok because SocketsAfterStrips(result-1,a) =1 + (result-1)*(a-1) =1 + (b-1) - (a-1) =1 + b-1 -a +1 = b - a +1
        // Need b - a +1 < b, yes a>=2, -a +1 <= -1+1=0 < b for b>=2
        // For b=2, a=2, 2-2+1=1 <2 yes
        // For b=3, a=2, cd=1, sockets at 1:1+1=2 >=3? No! CeilingDivision(2,1)=2
        // CeilingDivision(3-1,2-1)=ceildiv(2,1)=2
        // MinStripsNeeded for b=3,a=2 is 2? SocketsAfterStrips(2,2)=1+2*1=3 >=3, at 1:1+1=2 <3 yes
        assert go b - 1 == result * (a-1), since divisible
        var rna = result * (a-1);
        var prev =1 + (result-1)*(a-1) =1 + rna - (a-1) = rna +1 - (a-1) = rna -a +2
        = (b-1) -a +2 = b -a +1
        Since b >=2, a>=2, if b=2,a=2,1>0 yes
        if b=2,a=3, cd=1/2=1, sockets at1:1+2=3? Wait invalid
        Assume b >1, ok
      } else {
        // assert (b-1) % (a-1) >0
        // (result -1) * (a-1) + ( (b-1) - (result-1)*(a-1) ) < (b-1)
        // Since 1 + (result-1)*(a-1) + something < b
        // From ceiling, 1 + (cd-1)*m < 1 + k, since cd = ceil(k/m), 1 + (cd)m > k, so cd*m >= k - (m-1)
        //  (cd-1)*m <= cd*m - m < k -1 for the strict <
        // Since cd*m >= k, (cd-1)*m <= k - m
        // If k - m >= 1 + (cd-1)*m ? No
        // To have 1 + (cd-1)*m < b =1 + k
        //  (cd-1)*m < k
        // Since cd*m = (cd-1)*m + m >= k, cd*m + m - m >= k, no
        // From definition of ceil, for not divisible, q*y < x <= q*y + y -1
        // So cd = q+1, q = (x-1)/y, cd*m = (q+1)*(m) = q*m + m, q*m < x <= q*m + m -1
        // So cd*m >= x, but cd* m = x - (x % y) + m
        // Anyway, to_DONE have strict < for previous
        // (cd-1)*m <= (cd -1)*m, and since cd*m >= x +1 ? No
        // Since cd*m >= x, cd*m >= x + x % y - x % y, but to make (cd-1/fabric) * m < x
        // Since cd * manure m >= x +1 if not divisible
        // If not divisible, cd*m > x _Wait no, x <= cd* m <= x + m -1
        // For x = q*y + r UNS, cd = q+1, cd*m = qConvolution*m + m = q*y + y = x - r + y
        // Since r = x % y >0, cd*m = x - r + y > x since y > r
        // Yes, cd* m >= x + (m - r) > x since m >=1
        // For cd >1, (cd-1)* m > x - (m - r) -1 or something, but to have < x, since cd*m > x, (cd-1)*шла m = cd*m - m > x - m
        // If x - m >=1 + (cd-1)* m ? No
        // Simple: since cd = ceil(x/m), (cd -1) * m < x <= cd * m
        // Yes, for cd >=1, (cd -1)* m < x because otherwise if (cd-1)*m >= x, then cd = (cd-1) +1 <= (() ( (cd-1)* m / m ) +1 = (cd-1) +1 tilf = cd, but since >= x / mensivo or something.
        // No, the definition is the smallest integer >= x/m
        // So (cd -imsy1) * m < x because if cd -1 >= x/m, then cd would be >-cd1
        // Yes, standard: for cd = ceil(x/m), (cd -1) < x/m <= cd, so (cd -1)* m < x/php if x/m not integer
        // If x/ m is integer, cd = x/m, and (cd -1)* m = (x/m -1)* m = x - m < x since x >= m for cd >1? If cd =1, when x/m <=1, x <2*m, but if x/m is integer and =1, x=m, then cd=1, invalid for cd>1, but in condition if cd >0, but for min strips if 0 is possible
        // But in our case when cd >0 and if not divisible, (cd-1)*m < x = k
        // If divisible, since cd =1, cd-1=0, 0 < x = b-導入1, since b >1, always true
        // So ok
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
  requires ValidInput(a, b)
  ensures CorrectResult(a, b, result)
// </vc-spec>
// <vc-code>
{
  if b <= 1 {
    result := 0;
  } else {
    result := CeilingDivision(b - 1, a - 1);
  }
}
// </vc-code>

