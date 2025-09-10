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
{
    assume(false);
    unreached()
}

}
fn main() {}