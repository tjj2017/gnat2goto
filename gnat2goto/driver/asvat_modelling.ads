with Types;                   use Types;
with Atree;                   use Atree;
with Einfo;                   use Einfo;
package ASVAT_Modelling is
   Non_Det         : constant String := "Non_Det";
   Non_Det_In_Type : constant String := "Non_Det_In_Type";
   From_Unit       : constant String := "From_Unit";

   Model_List : constant String :=
     (""
        & Non_Det         & '#'
        & Non_Det_In_Type & '#'
        & From_Unit       & '#'
     );

   type Model_Index is range 0 .. Model_List'Length;

   function Find_Model (S : String) return Model_Index;

   function Is_Model (E : Entity_Id) return Boolean;

   function Is_Model_Sort (E : Entity_Id; Model : String) return Boolean;

   procedure Make_Model (E : Entity_Id)
   with Pre => Is_Model (E);

   function Rename_Import (E : Entity_Id) return String
     with Pre => Ekind (E) in E_Variable | E_Constant;

end ASVAT_Modelling;
