/* 
  This assignment illustrates how specifications (invariants and 
  preconditions)  written in a formal language can help in removing 
  errors in code. 
 */


class FixedTaxpayer {
  /* isFemale is true iff the person is female */
  boolean isFemale;

  /* isMale is true iff the person is male */
  boolean isMale;

  int age; 

  boolean isMarried; 

  /* Reference to spouse if person is married, null otherwise */
  FixedTaxpayer spouse; 

  /* Constant default income tax allowance */
  static final int DEFAULT_ALLOWANCE = 5000;

  /* Constant income tax allowance for Older FixedTaxpayers over 65 */
  static final  int ALLOWANCE_OAP = 7000;

  /* Income tax allowance */
  int tax_allowance; 

  int income; 

  Taxpayer(boolean babyboy, FixedTaxpayer ma, FixedTaxpayer pa) {
    age = 0;
    isMarried = false;
    this.isMale = babyboy;
    this.isFemale = !babyboy;
    mother = ma;
    father = pa;
    spouse = null;
    income = 0;
    tax_allowance = DEFAULT_ALLOWANCE;
    /* The line below makes explicit the assumption that a new Taxpayer is not 
      * married to anyone yet*/
    //@ assume (\forall FixedTaxpayer p; p.spouse != this); 
  } 

  //@ requires new_spouse != null;
  void marry(FixedTaxpayer new_spouse) {
    spouse = new_spouse;
    isMarried = true;
  }
  
  void divorce() {
    spouse.spouse = null;
    spouse = null;
    isMarried = false;
  }

  /* Transfer part of tax allowance to own spouse */
  void transferAllowance(int change) {
    tax_allowance = tax_allowance - change;
    spouse.tax_allowance = spouse.tax_allowance + change;
  }

  void haveBirthday() {
    age++;
  }
}
