with Types;                   use Types;
with Atree;                   use Atree;
with Sinfo;                   use Sinfo;
with Sem_Util;                use Sem_Util;
with Snames;                  use Snames;
package ASVAT_Modelling is
   Non_Det         : constant String := "non_det";
   Non_Det_In_Type : constant String := "non_det_in_type";
   Replace_With    : constant String := "replace_with";

   Model_List : constant String :=
     (""
        & Non_Det          & '#'
        & Non_Det_In_Type  & '#'
        & Replace_With     & '#'
     );

   function Get_Import_Convention (N : Node_Id) return String
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (N) = Pragma_Import;

   function Get_Import_External_Name (N : Node_Id) return String
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (N) = Pragma_Import;
   --  Returns null string if the External_Name parameter is not present.

   function Get_Import_Link_Name (N : Node_Id) return String
   with Pre => Nkind (N) = N_Pragma and then
               Get_Pragma_Id (N) = Pragma_Import;
   --  Returns null string if the Link_Name parameter is not present.

   function Is_Model (E : Entity_Id) return Boolean;

   function Is_Model_String (S : String) return Boolean;

   function Is_Model_Sort (E : Entity_Id; Model : String) return Boolean;

   procedure Make_Model (E : Entity_Id)
   with Pre => Is_Model (E);

end ASVAT_Modelling;
