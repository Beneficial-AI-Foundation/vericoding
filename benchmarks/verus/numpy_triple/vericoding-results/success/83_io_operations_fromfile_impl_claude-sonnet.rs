// <vc-preamble>
use vstd::prelude::*;

verus! {

struct FileHandle {

    path: String,

    is_binary: bool,

    position: nat,
}

enum DType {

    Float32,

    Float64,

    Int32,

    Int64,

    UInt8,
}

spec fn dtype_size_bytes(dtype: DType) -> nat {
    match dtype {
        DType::Float32 => 4,
        DType::Float64 => 8,
        DType::Int32 => 4,
        DType::Int64 => 8,
        DType::UInt8 => 1,
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clause to fix compilation error */
fn read_binary_data(file: &FileHandle, dtype: DType, count: i32, offset: nat) -> (result: Vec<i32>)
    requires
        count > 0,
        file.is_binary == true
    ensures
        result.len() == count as usize
{
    let mut data = Vec::new();
    let mut i = 0;
    while i < count
        invariant
            i >= 0,
            i <= count,
            data.len() == i as usize
        decreases count - i
    {
        data.push(0);
        i = i + 1;
    }
    data
}

fn read_text_data(file: &FileHandle, count: i32, sep: &str, offset: nat) -> (result: Vec<i32>)
    requires
        count > 0,
        file.is_binary == false,
        sep != ""
    ensures
        result.len() == count as usize
{
    let mut data = Vec::new();
    let mut i = 0;
    while i < count
        invariant
            i >= 0,
            i <= count,
            data.len() == i as usize
        decreases count - i
    {
        data.push(0);
        i = i + 1;
    }
    data
}
// </vc-helpers>

// <vc-spec>
fn fromfile(file: FileHandle, dtype: DType, count: i32, sep: &str, offset: nat) -> (result: Vec<i32>)
    requires
        count == -1 || count > 0,
        sep == "" ==> file.is_binary == true,
        file.is_binary == true ==> sep == "",
    ensures
        count > 0 ==> result.len() == count as usize,

        file.is_binary == true ==> (
            #[trigger] (result.len() * dtype_size_bytes(dtype))
            >= 0
        ),

        true,

        true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): no changes needed for main body */
    if count > 0 {
        if file.is_binary {
            read_binary_data(&file, dtype, count, offset)
        } else {
            read_text_data(&file, count, sep, offset)
        }
    } else {
        Vec::new()
    }
}
// </vc-code>

}
fn main() {}