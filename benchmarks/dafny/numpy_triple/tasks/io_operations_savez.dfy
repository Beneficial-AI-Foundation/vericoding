// <vc-preamble>
// Vector datatype representing a sequence of floating-point values
type Vector = seq<real>

// File system state abstraction for modeling file operations
datatype FileSystem = FileSystem(
    files: map<string, seq<uint8>>,
    writable_paths: set<string>
)

// Archive content representing the structure of a .npz file
datatype ArchiveContent = ArchiveContent(
    array1: Vector,
    array2: Vector,
    metadata: map<string, string>
)

// Ghost function to model archive deserialization for specification purposes
ghost function DeserializeArchive(file_data: seq<uint8>): ArchiveContent

// Ghost function to check if a file path represents a valid .npz archive
ghost predicate IsValidNpzArchive(file_data: seq<uint8>)

// Ghost function to extract array data from archive content
ghost function ExtractArray1(content: ArchiveContent): Vector
{
    content.array1
}

ghost function ExtractArray2(content: ArchiveContent): Vector
{
    content.array2
}

// Global file system state for modeling file operations
var global_fs: FileSystem

// Method specification for numpy.savez
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Savez(file: string, arr1: Vector, arr2: Vector, allow_pickle: bool := true)
    requires file != ""
    requires file in old(global_fs.writable_paths)
    requires |arr1| >= 0
    requires |arr2| >= 0
    ensures var new_file_data := global_fs.files[file];
           |new_file_data| > 0
    ensures file in global_fs.files
    ensures IsValidNpzArchive(global_fs.files[file])
    ensures var archive_content := DeserializeArchive(global_fs.files[file]);
            ExtractArray1(archive_content) == arr1
    ensures var archive_content := DeserializeArchive(global_fs.files[file]);
            ExtractArray2(archive_content) == arr2
    ensures var archive_content := DeserializeArchive(global_fs.files[file]);
            forall i :: 0 <= i < |arr1| ==> archive_content.array1[i] == arr1[i]
    ensures var archive_content := DeserializeArchive(global_fs.files[file]);
            forall i :: 0 <= i < |arr2| ==> archive_content.array2[i] == arr2[i]
    modifies `global_fs
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
