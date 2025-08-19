//IMPL
method has_close_elements(numbers: seq<real>, threshold: real) returns (res: bool)
 requires threshold >= 0.0
 ensures res ==> exists i: int, j: int :: 0 <= i < |numbers| && 0 <= j < |numbers| && i != j && (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) < threshold
 ensures !res ==> (forall i: int, j: int :: 1 <= i < |numbers| && 0 <= j < i ==> (if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j]) >= threshold)
{
    /* code modified by LLM (iteration 1): added early return for empty or single-element sequences */
    if |numbers| <= 1 {
        return false;
    }
    
    var i := 1;
    while i < |numbers|
        /* code modified by LLM (iteration 1): added proper loop invariant bounds */
        invariant 1 <= i <= |numbers|
        invariant forall x: int, y: int :: 1 <= x < i && 0 <= y < x ==> (if numbers[x] - numbers[y] < 0.0 then numbers[y] - numbers[x] else numbers[x] - numbers[y]) >= threshold
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant forall x: int, y: int :: 1 <= x < i && 0 <= y < x ==> (if numbers[x] - numbers[y] < 0.0 then numbers[y] - numbers[x] else numbers[x] - numbers[y]) >= threshold
            invariant forall y: int :: 0 <= y < j ==> (if numbers[i] - numbers[y] < 0.0 then numbers[y] - numbers[i] else numbers[i] - numbers[y]) >= threshold
        {
            var diff := if numbers[i] - numbers[j] < 0.0 then numbers[j] - numbers[i] else numbers[i] - numbers[j];
            if diff < threshold {
                return true;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    return false;
}