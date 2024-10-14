**RAG-LLM-SPC-SVA**

**Enhanced VLSI Assertion Generation: Aligning with High-Level Specifications and Minimizing LLM Hallucinations Using RAG**


**Overview**

This repository provides a framework for generating SystemVerilog Assertions (SVAs) for VLSI design verification using a Retrieval-Augmented Generation (RAG) approach in conjunction with Large Language Models (LLMs). 
The method aims to ensure conformity to high-level specifications (HLS) and reduce the potential for hallucinations inherent in LLM-generated assertions.

----------------------------------------------------------------------------------------------------------------------------------------------------------------------------

**Steps**

**i) Data Preparation (/Data)**

  * Case Study - High-Level Specification (HLS) Document:
  
    * Source document: AMBA AX4 Lite Protocol PDF (AMBA AXI Protocol Specification: https://developer.arm.com/documentation/ihi0022/).
    
    * Convert the PDF document into Markdown format for structured referencing.

  * Designer Specifications:
  
    * Define designer-side specifications for intended SystemVerilog Assertions (SVAs) generation.

  * Golden HDL Desig):
    * Use a verified golden HDL for comparison and validation of generated assertions.

----------------------------------------------------------------------------------------------------------------------------------------------------------------------------

**ii) Experimental Steps & Results (GPT-3.5-Results)**

  * Setup and API Key:

    * Provide the OpenAI API key for chat completion.

  * File References:

    * Ensure references to the HLS document, designer specifications, and golden HDL are accessible within the setup.

  * Prompt Engineering:

    * Utilize prompts from the prompt-engineering file to assign specific roles to the LLM for efficient and contextually accurate assertion generation.

  * Execution (after configuration, execute .ipynb file ): 

    * Run the code (Enhanced_VLSI_Assertion_Generation_Conforming_to_High_Level_Specifications_and_Reducing_LLM_Hallucinations_with_RAG.ipynb) to generate assertions and knowledge-based results from the LLM.
    
    * Store the generated assertions and results for subsequent validation.

----------------------------------------------------------------------------------------------------------------------------------------------------------------------------

**iii) Evaluation Using Bounded Model Checking (BMC)**

  * Validation Setup:

    * Employ formal property verification through bounded model checking (BMC) to verify generated assertions against the HDL (RTL) design.

  * Tool Setup:

    * Download and install the Tabby-CAD toolset for BMC (https://www.yosyshq.com/tabby-cad-datasheet).

  * Assertion Integration:

    * Insert the RAG-LLM-generated assertions into the golden DUV code.

  * Execution and Verification:

    * Run Tabby-CAD to execute and validate the assertions, comparing outcomes against the original DUV specifications.

----------------------------------------------------------------------------------------------------------------------------------------------------------------------------

**Applicability**

  The RAG-LLM approach can be extended to other case studies and is compatible with future versions of foundation/ language models, such as GPTs, Llama, and beyond.
