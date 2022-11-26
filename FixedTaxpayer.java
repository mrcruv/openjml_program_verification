/* 
  This assignment illustrates how specifications (invariants and 
  preconditions)  written in a formal language can help in removing 
  errors in code. 
 */


class FixedTaxpayer {
  //@ invariant (this.isFemale == true <==> this.isMale == false);
  //@ invariant (this.isMarried == false <==> this.spouse == null);
  //@ invariant (this.spouse != null ==> this.isMale == this.spouse.isFemale);
  //@ invariant (this.spouse != null ==> this.spouse.spouse == this);
  //@ invariant (0 <= this.tax_allowance <= Integer.MAX_VALUE);
  //@ invariant (this.age <= Integer.MAX_VALUE);

  /* isFemale is true iff the person is female */
  boolean isFemale;

  /* isMale is true iff the person is male */
  boolean isMale;

  int age; 

  boolean isMarried; 

  /* Reference to spouse if person is married, null otherwise */
  /*@ nullable */ FixedTaxpayer spouse; 

  /* Constant default income tax allowance */
  static final int DEFAULT_ALLOWANCE = 5000;

  /* Constant income tax allowance for Older FixedTaxpayers over 65 */
  static final  int ALLOWANCE_OAP = 7000;

  /* Income tax allowance */
  int tax_allowance; 

  int income; 

  FixedTaxpayer mother;

  FixedTaxpayer father;

  FixedTaxpayer(boolean babyboy, FixedTaxpayer ma, FixedTaxpayer pa) {
    this.age = 0;
    this.isMarried = false;
    this.isMale = babyboy;
    this.isFemale = !babyboy;
    this.mother = ma;
    this.father = pa;
    this.spouse = null;
    this.income = 0;
    this.tax_allowance = FixedTaxpayer.DEFAULT_ALLOWANCE;
    /* The line below makes explicit the assumption that a new FixedTaxpayer is not 
      * married to anyone yet*/
    //@ assume (\forall FixedTaxpayer p; p.spouse == null && p.spouse != this); 
  } 

  //@ requires (new_spouse != null && this.spouse == null && new_spouse.spouse == null);
  void marry(FixedTaxpayer new_spouse) {
    if (new_spouse == null || new_spouse.spouse != null || this.isMale != new_spouse.isFemale) return;
    this.spouse = new_spouse;
    this.isMarried = true;
    new_spouse.spouse = this;
    new_spouse.isMarried = true;
  }
  
  //@ requires (this.spouse != null);
  void divorce() {
    if (this.spouse == null) return;
    this.spouse.isMarried = false;
    this.spouse.spouse = null;
    this.isMarried = false;
    this.spouse = null;
  }

  /* Transfer part of tax allowance to own spouse */
  //@ requires (this.spouse != null);
  //@ requires (change > 0 && change <= this.tax_allowance && change <= Integer.MAX_VALUE - this.spouse.tax_allowance);
  //@ ensures (this.tax_allowance + this.spouse.tax_allowance) == \old(this.tax_allowance + this.spouse.tax_allowance);
  void transferAllowance(int change) {
    if (this.spouse == null) return;
    if (change <= 0 || change > this.tax_allowance || change > Integer.MAX_VALUE - this.spouse.tax_allowance) return;
    this.tax_allowance = this.tax_allowance - change;
    this.spouse.tax_allowance = this.spouse.tax_allowance + change;
  }

  //@ requires (this.age < Integer.MAX_VALUE);
  //@ ensures (this.age == 65 && this.tax_allowance <= Integer.MAX_VALUE - 2000 ==> this.tax_allowance == \old(this.tax_allowance) + 2000);
  void haveBirthday() {
    if (this.age < Integer.MAX_VALUE) age++;
    else return;
    if (this.age == 65 && this.tax_allowance <= Integer.MAX_VALUE - 2000) this.tax_allowance = this.tax_allowance + 2000;
  }
}
