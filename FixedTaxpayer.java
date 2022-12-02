/* 
  This assignment illustrates how specifications (invariants and 
  preconditions)  written in a formal language can help in removing 
  errors in code. 
 */


class FixedTaxpayer {
  //1.1: persons are either male or female.
  //@ invariant this.isFemale == true <==> this.isMale == false;

  //1.2: persons can only marry people of the opposite sex.
  //@ invariant this.spouse != null ==> this.isMale == this.spouse.isFemale;

  //1.2a: if person x is married to person y, then person y should of course also be married and to person x.
  //@ invariant this.spouse != null ==> this.spouse.spouse == this;

  //if a person x is married to person y, then x's spouse cannot be null (and viceversa).*
  //@ invariant this.isMarried == false <==> this.spouse == null;

  //tax allowance must be non negative.*
  //@ invariant this.tax_allowance >= 0;
  //age must be non negative.*
  //@ invariant this.age >= 0;

  //every person has an income tax allowance on which no tax is paid, there is a default tax allowance of 5000 per individual and only income above this amount is taxed.*
  //@ invariant this.spouse == null && this.age < 65 ==> this.tax_allowance == FixedTaxpayer.DEFAULT_ALLOWANCE;

  //2.2: married persons can pool their tax allowance, as long as the sum of their tax allowances remains the same (below, this constraint is expressed as postcondition on method transferAllowance).
  //3.1: the new government introduces a measure that people aged 65 and over have a higher tax allowance of 7000 (below, this constraint is expressed as postcondition on method haveBirthday).
  //@ invariant this.spouse == null && this.age >= 65 ==> this.tax_allowance == FixedTaxpayer.ALLOWANCE_OAP;
  //@ invariant this.spouse != null && this.age < 65 && this.spouse.age < 65 ==> this.tax_allowance + this.spouse.tax_allowance == (FixedTaxpayer.DEFAULT_ALLOWANCE + FixedTaxpayer.DEFAULT_ALLOWANCE);
  //@ invariant this.spouse != null && this.age >= 65 && this.spouse.age < 65 ==> this.tax_allowance + this.spouse.tax_allowance == (FixedTaxpayer.ALLOWANCE_OAP + FixedTaxpayer.DEFAULT_ALLOWANCE);
  //@ invariant this.spouse != null && this.age >= 65 && this.spouse.age >= 65 ==> this.tax_allowance + this.spouse.tax_allowance == (FixedTaxpayer.ALLOWANCE_OAP + FixedTaxpayer.ALLOWANCE_OAP);

  boolean isFemale;

  boolean isMale;

  int age; 

  boolean isMarried; 

  //a person's spouse can be null.*
  /*@ nullable */ FixedTaxpayer spouse; 

  static final int DEFAULT_ALLOWANCE = 5000;

  static final  int ALLOWANCE_OAP = 7000;

  int tax_allowance; 

  int income; 

  FixedTaxpayer mother;

  FixedTaxpayer father;

  FixedTaxpayer(boolean babyboy, FixedTaxpayer ma, FixedTaxpayer pa) {
    this.age = 0;
    this.isMarried = false;
    this.isMale = babyboy;
    this.isFemale = !babyboy;
    this.mother = ma; //beware: aliasing!
    this.father = pa; //beware: aliasing!
    this.spouse = null;
    this.income = 0;
    this.tax_allowance = FixedTaxpayer.DEFAULT_ALLOWANCE;
    /* The line below makes explicit the assumption that a new FixedTaxpayer is not 
      * married to anyone yet*/
    //@ assume (\forall FixedTaxpayer p; p.spouse == null && p.spouse != this); 
  } 

  //constraints to limit possible side-effects.*
  //@ assignable this.spouse, this.isMarried, this.spouse.spouse, this.spouse.isMarried;
  //a person x can marry a person y if and only if either x and y are not married yet.*
  //@ requires new_spouse != null && this.spouse == null && new_spouse.spouse == null;
  void marry(FixedTaxpayer new_spouse) {
    if (this.isMale != new_spouse.isFemale) return;
    this.spouse = new_spouse; //beware: aliasing!
    this.isMarried = true;
    this.spouse.spouse = this; //beware: aliasing!
    this.spouse.isMarried = true;
  }
  
  //constraints to limit possible side-effects.*
  //@ assignable this.tax_allowance, this.spouse.tax_allowance, this.spouse.isMarried, this.spouse.spouse, this.isMarried, this.spouse;
  //a person x can divorce if and only if x's spouse is not null.*
  //@ requires this.spouse != null;
  void divorce() {
    this.tax_allowance = this.age < 65 ? FixedTaxpayer.DEFAULT_ALLOWANCE : FixedTaxpayer.ALLOWANCE_OAP;
    this.spouse.tax_allowance = this.spouse.age < 65 ? FixedTaxpayer.DEFAULT_ALLOWANCE : FixedTaxpayer.ALLOWANCE_OAP;
    this.spouse.isMarried = false;
    this.spouse.spouse = null;
    this.isMarried = false;
    this.spouse = null;
  }

  //preconditions for avoiding overflows and underflows.*
  //@ requires change + Integer.MIN_VALUE <= this.tax_allowance;
  //@ requires change <= Integer.MAX_VALUE - this.spouse.tax_allowance;
  //constraints to limit possible side-effects.*
  //@ assignable this.tax_allowance, this.spouse.tax_allowance;
  //a person x can transfer allowance only if x's spouse is not null.*
  //@ requires this.spouse != null;
  //a person x can transfer allowance only if change is non negative and not greater than x's tax allowance.*
  //@ requires change > 0 && change <= this.tax_allowance;
  //2.2: married persons can pool their tax allowance, as long as the sum of their tax allowances remains the same.
  //@ ensures this.tax_allowance + this.spouse.tax_allowance == \old(this.tax_allowance) + \old(this.spouse.tax_allowance);
  void transferAllowance(int change) throws ArithmeticException {
    this.tax_allowance = this.tax_allowance - change;
    this.spouse.tax_allowance = this.spouse.tax_allowance + change;
  }

  //preconditions for avoiding overflows.*
  //@ requires this.age <= Integer.MAX_VALUE - 1;
  //@ requires this.age == 64 ==> this.tax_allowance <= Integer.MAX_VALUE - (FixedTaxpayer.ALLOWANCE_OAP - FixedTaxpayer.DEFAULT_ALLOWANCE);
  //constraints to limit possible side-effects.*
  //@ assignable this.age, this.tax_allowance;
  //3.1: the new government introduces a measure that people aged 65 and over have a higher tax allowance of 7000.
  //@ ensures this.age == 65 ==> this.tax_allowance == \old(this.tax_allowance) + (FixedTaxpayer.ALLOWANCE_OAP - FixedTaxpayer.DEFAULT_ALLOWANCE);
  void haveBirthday() throws ArithmeticException {
    this.age = this.age + 1;
    if (this.age == 65) this.tax_allowance = this.tax_allowance + (FixedTaxpayer.ALLOWANCE_OAP - FixedTaxpayer.DEFAULT_ALLOWANCE);
  }
}
