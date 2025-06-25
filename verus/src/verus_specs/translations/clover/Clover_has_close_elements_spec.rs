pub fn has_close_elements(numbers: Seq<real>, threshold: real) -> (res: bool)
    requires(threshold >= 0.0)
    ensures(res ==> exists|i: int, j: int| 0 <= i < numbers.len() && 0 <= j < numbers.len() && i != j && (if numbers[i] - numbers[j] < 0.0 { numbers[j] - numbers[i] } else { numbers[i] - numbers[j] }) < threshold)
    ensures(!res ==> (forall|i: int, j: int| 1 <= i < numbers.len() && 0 <= j < i ==> (if numbers[i] - numbers[j] < 0.0 { numbers[j] - numbers[i] } else { numbers[i] - numbers[j] }) >= threshold))
{
}