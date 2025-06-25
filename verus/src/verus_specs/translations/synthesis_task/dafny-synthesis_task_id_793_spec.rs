pub fn last_position(arr: &mut [i32], elem: i32) -> (pos: i32)
    requires(
        arr.len() > 0,
        forall|i: usize, j: usize| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
    )
    ensures(|pos: i32|
        pos == -1 || (0 <= pos < arr.len() && arr[pos as usize] == elem && (pos <= arr.len() as i32 - 1 || arr[(pos + 1) as usize] > elem)),
        forall|i: usize| 0 <= i < arr.len() ==> arr[i] == old(arr)[i]
    )
{
}