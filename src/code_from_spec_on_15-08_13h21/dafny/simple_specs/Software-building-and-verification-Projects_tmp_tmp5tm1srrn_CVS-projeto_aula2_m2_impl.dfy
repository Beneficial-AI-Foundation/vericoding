//IMPL 

// 5b
method m2(x: nat) returns (y: int)
 requires x <= -1
 ensures y > x && y < x
{
    // The precondition x <= -1 where x: nat is impossible
    // since nat values are >= 0, so this code is unreachable
    y := 0;
}