with Types;                   use Types;
with Atree;                   use Atree;
with Sinfo;                   use Sinfo;
with Sem_Util;                use Sem_Util;
with Snames;                  use Snames;
with Ireps;                    use Ireps;
package ASVAT_Modelling is
   type Model_Sorts is (Not_A_Model, Non_Det, Non_Det_In_Type, Replace_With);
   subtype Valid_Model is Model_Sorts range Non_Det .. Model_Sorts'Last;

   function Do_Non_Det_Attribute
     (N : Node_Id; Type_Name : String) return Irep
   with Pre => Nkind (N) = N_Attribute_Reference;

   function Do_Non_Det_Function_Call
     (Fun_Name : String; Loc : Source_Ptr) return Irep;

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

   function Is_Model_Sort (E : Entity_Id; Model : Model_Sorts) return Boolean;

   procedure Make_Model (E : Entity_Id)
   with Pre => Is_Model (E);

   procedure Make_Non_Det_Function (Fun_Name, Type_Name : String;
                                    Loc : Source_Ptr);
end ASVAT_Modelling;
