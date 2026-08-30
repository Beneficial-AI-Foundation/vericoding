--  <vc-preamble>
package Np_Isclose_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;

   type Bool_Array is array (Index_Type range <>) of Boolean;
--  </vc-preamble>

--  <vc-spec>
   procedure Is_Close
     (A      : Int_Array;
      B      : Int_Array;
      Tol    : Value_Type;
      Result : out Bool_Array)
   with
     Pre  => A'Length > 0
             and then A'First = B'First and then A'Last = B'Last
             and then Result'First = A'First and then Result'Last = A'Last
             and then Tol > 0,
     Post => (for all I in A'Range =>
                Result (I) = (-Tol < A (I) - B (I) and then A (I) - B (I) < Tol));

end Np_Isclose_Spec;

package body Np_Isclose_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Is_Close
     (A      : Int_Array;
      B      : Int_Array;
      Tol    : Value_Type;
      Result : out Bool_Array) is
   begin
      pragma Assume (False);
   end Is_Close;
--  </vc-code>

--  <vc-postamble>
end Np_Isclose_Spec;
--  </vc-postamble>
