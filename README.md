# Modelling GDPR-Compliance Based on Defeasible Logic Reasoning

**Project Title:** Threat Modelling Technique for GDPR-Compliance based on Defeasible Logic Reasoning

**Authors:** Azam Naila, Chak Alex, Michala AnnaLito, Ansari Shuja, Nguyen Truong

**Affiliation:**
- School of Computing Science, University of Glasgow, Glasgow, United Kingdom
- James Watt School of Engineering, University of Glasgow, Glasgow, United Kingdom

## Source Code and Project Repository
The complete source code for the platform demonstration referenced in our paper can be found at [this GitHub repository](https://github.com/nailaazam/Efficient_DeLP_GDPR-Project/tree/master/Efficient_DeLP_GDPR).

## Source Code Structure

The source code is organized into several parts, as described below:

- **Defeasible Logic Programming (DeLP):**
  - Location: `Efficient_DeLP_GDPR-Project/Efficient_DeLP_GDPR/src/DeLP_GDPR/delp/`

- **Demonstration for the Fitbit Use Case:**
  - Location: `Efficient_DeLP_GDPR-Project/Efficient_DeLP_GDPR/knowledge_base/`

- **Reasoning Mechanism:**
 - The implementation of "UNDECIDED Results Handelers" and the evaluation of the Reasoner's "Complexity" can be found here:
  - Location: `./reasoner`

- **Supporting Classes for DeLP:**
  - Parser: `./parse`
  - Semantics: `./semantics`
  - Syntax: `./syntax`

- **Additional Components:**
  - These are inherited from TweetyProject and found under `Efficient_DeLP_GDPR/src/Efficient_DeLP_GDPR/`, including modules for:
    - DUNG
    - Graphs
    - Logics
    - Math and Maths

## Knowledge Bases

Defeasible knowledge bases for different scenarios (i.e., horizontal complexity and vertical complexity), including the Fitbit use-case, are located in `Efficient_DeLP_GDPR-Project/Efficient_DeLP_GDPR/knowledge_base/`.

- **Test Cases for System Performance Evaluation:**
  - Location: `./knowledge_base/testcases`

## System Performance Evaluation Results

The results, including execution times for different types of queries ("YES/NO/UNDECIDED"), are found in `Efficient_DeLP_GDPR-Project/Efficient_DeLP_GDPR/results.txt`.

## Contact Information

For further information or inquiries, please contact:
- **Naila Azam**
  - Email: nazamali37@gmail.com or n.naila.1@research.gla.ac.uk
