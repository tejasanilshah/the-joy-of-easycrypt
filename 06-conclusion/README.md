# Conclusion

Working through the material should give you a basic grasp of how EasyCrypt works, and the ability to work with some of the tactics. Admittedly, this work is by no means complete since we barely scratched the surface of what EasyCrypt is capable of doing and the current state of the art when it comes to cryptography.

## Future work:
1. **Covering more EasyCrypt concepts**:
    Notably the next few chapters should present the readers with practice on Probabilistic Hoare logic (pHL), and Probabilistic Relational Hoare logic (pRHL). While working with these logics the material can already start introducing cryptography.
2. **Further depth of already covered concepts**:
    Our treatment of the tactics has been such that it gives the readers a quick idea of what they do, however many tactics have different variations and can use a more detailed explanation. For instance, the `move =>` tactic has several introduction patterns that we haven't addressed in this work.
3. **Automated scripts to create beautiful documentation**:
    Our current process of writing this material has been to first write a lot of material in the `.ec` files and then manually pick the important concepts to highlight in the theory. Or first write some theory in $\LaTeX$ and then create the `.ec` files to provide practice for the ideas covered. This creates the problem of both the documents diverging and additional work to fix these issues of diverging files. This problem can be avoided if we create scripts that can read the `.ec`, and automatically create readable documentation based on unique delimiters in the text. This would simplify the process of writing educational material quite a lot.


## Caveats: 
This repo has been created on a best effort basis, and as outlined above needed a lot of manual effort. Meaning it could contain errors here and there. If you find any errors feel free to send a pull request with fixes.
If you can make this project better even better, fork it and make it better.

We provide the [PDF file](https://github.com/tejasanilshah/the-joy-of-easycrypt/blob/master/assets/Shah_CS_2022.pdf) which has syntax highlighting and has been proofread a couple of times as well. We recommend using that file + `.ec` files as the primary mode of consumption.

Additionally, we also provide the $\LaTeX$ [project](https://github.com/tejasanilshah/the-joy-of-easycrypt/blob/master/assets/Shah_CS_2022.zip) as is and a [read-only overleaf project](https://www.overleaf.com/read/brvftqdzgxnp) for those interested in the content and who want to use the syntax highlighting.
