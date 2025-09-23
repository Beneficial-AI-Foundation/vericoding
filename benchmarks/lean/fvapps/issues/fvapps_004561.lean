-- <vc-preamble>
def FileMaster.extension (fm: FileMaster) : String :=
  sorry

def FileMaster.filename (fm: FileMaster) : String :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FileMaster.dirpath (fm: FileMaster) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem filemaster_extension_matches_input (dirpath name ext : String) :
  let filepath := dirpath ++ name ++ "." ++ ext
  let fm := FileMaster.mk filepath
  FileMaster.extension fm = ext :=
sorry

theorem filemaster_filename_matches_input (dirpath name ext : String) :
  let filepath := dirpath ++ name ++ "." ++ ext
  let fm := FileMaster.mk filepath
  FileMaster.filename fm = name :=
sorry

theorem filemaster_dirpath_matches_input (dirpath name ext : String) :
  let filepath := dirpath ++ name ++ "." ++ ext
  let fm := FileMaster.mk filepath
  FileMaster.dirpath fm = dirpath :=
sorry

theorem filemaster_house_png_example :
  let fm := FileMaster.mk "/Users/person1/Pictures/house.png"
  FileMaster.extension fm = "png" ∧ 
  FileMaster.filename fm = "house" ∧
  FileMaster.dirpath fm = "/Users/person1/Pictures/" :=
sorry

theorem filemaster_index_html_example :
  let fm := FileMaster.mk "/var/www/index.html"
  FileMaster.extension fm = "html" ∧
  FileMaster.filename fm = "index" ∧ 
  FileMaster.dirpath fm = "/var/www/" :=
sorry
-- </vc-theorems>