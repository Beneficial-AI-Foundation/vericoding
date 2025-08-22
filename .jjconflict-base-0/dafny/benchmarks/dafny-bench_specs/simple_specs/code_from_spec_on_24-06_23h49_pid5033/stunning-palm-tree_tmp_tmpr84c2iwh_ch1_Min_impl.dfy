//IMPL 
method Min (x: int, y: int) returns (r: int)
/* code modified by LLM (iteration 1): Fixed method structure by moving ensures clauses before body and correcting brace placement */
ensures r <= x && r <= y
ensures r == x || r == y 
{
    if x <= y {
        r := x;
    } else {
        r := y;
    }
}