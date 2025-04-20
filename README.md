This folder contains the EasyCrypt (https://github.com/EasyCrypt/easycrypt) proofs of the commitment schemes from "Constant-Size Commitments to Polynomials and
Their Applications?" by
Aniket Kate, Gregory M. Zaverucha, and Ian Goldberg (https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf)

We proved concrete versions of:
    Theorem 1 and 2 broken into separate lemmas for each of the four sub-properties
    
The following are files and their contents:
- AddList.ec - contains additional lemmas about lists
- Bilinear.ec - defines a symmetric bilinear group and various helpful lemmas. It also defines the discrete log and t-SDH assumptions in the base group.
- AddPoly.ec - contains additional lemmas on polynomials
- PolyCom.ec - defines a polynomial commitment scheme
- PolyComDL.ec - defines PolyCom_DL instance and proves the four required properties
- PolyComPed.ec - defines PolyCom_Ped instance and proves the four required properties

These proofs were developed and tested with the following configuration:
EasyCrypt commit - 9eaff01c7..22fe124e9
known provers: Alt-Ergo@2.4.2, Alt-Ergo[FPA]@2.4.2, CVC4@1.8.0, CVC4[counterexamples]@1.8.0, CVC4[strings]@1.8.0, CVC4[strings+counterexamples]@1.8.0, CVC5@1.0.5, CVC5[counterexamples]@1.0.5, CVC5[strings]@1.0.5, CVC5[strings+counterexamples]@1.0.5, Z3@4.12.6, Z3[counterexamples]@4.12.6, Z3[noBV]@4.12.6

To verify the EasyCrypt files run:

easycrypt AddDistr.ec; easycrypt AddList.ec; easycrypt Bilinear.ec; easycrypt AddPoly.ec; easycrypt PolyCom.ec; easycrypt PolyComDL.ec; easycrypt PolyComPed.ec
