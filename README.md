---
layout    : page
title     : Getting Started
prev      : /Preface/
permalink : /GettingStarted/
next      : /Naturals/
---

<!-- Status & Version Badges -->

[![Calendar Version][plfa-calver]][plfa-latest]
[![Agda][agda-version]][agda]
[![agda-stdlib][agda-stdlib-version]][agda-stdlib]


## Dependencies for users
You can read PLFA [online][plfa] without installing anything. However, if you wish to interact with the code or complete the exercises, you need several things:

  - [Stack](#install-the-haskell-tool-stack)
  - [Git](#install-git)
  - [Agda](#install-agda-using-stack)
  - [Agda standard library](#install-plfa-and-the-agda-standard-library)
  - [PLFA](#install-plfa-and-the-agda-standard-library)

PLFA is tested against specific versions of Agda and the standard library, which are shown in the badges above. Agda and the standard library change rapidly, and these changes often break PLFA, so using older or newer versions usually causes problems.

There are several versions of Agda and its standard library online. If you are using a package manager, like Homebrew or Debian apt, the version of Agda available there may be out-of date. Furthermore, Agda is under active development, so if you install the development version from the GitHub, you might find the developers have introduced changes which break the code here. Therefore, it’s important to have the specific versions of Agda and the standard library shown above.


### On macOS: Install the XCode Command Line Tools
On macOS, you’ll need to install the [XCode Command Line Tools][xcode]. For most versions of macOS, you can install these by running the following command:
```bash
xcode-select --install
```

### Install the Haskell Tool Stack
Agda is written in Haskell, so to install it we’ll need the *Haskell Tool Stack*, or *Stack* for short. Stack is a program for managing different Haskell compilers and packages:

- *On UNIX and macOS.* If your package manager has a package for Stack, that’s probably your easiest option. For instance, Homebrew on macOS  and APT on Debian offer the “haskell-stack” package. Otherwise, you can follow the instructions on [the Stack website][haskell-stack]. Usually, Stack installs binaries at “HOME/.local/bin”. Please ensure this is on your PATH, by including the following in your shell configuration, e.g., in `HOME/.bash_profile`:
  ```bash
  export PATH="${HOME}/.local/bin:${PATH}"
  ```
  Finally, ensure that you’ve got the latest version of Stack, by running:
  ```bash
  stack upgrade
  ```

- *On Windows.* There is a Windows installer on [the Stack website][haskell-stack].


### Install Git
If you do not already have Git installed, see [the Git downloads page][git].


### Install Agda using Stack
The easiest way to install a *specific version* of Agda is using [Stack][haskell-stack]. You can get the required version of Agda from GitHub, either by cloning the repository and switching to the correct branch, or by downloading [the zip archive][agda]:
```bash
git clone https://github.com/agda/agda.git
cd agda
git checkout v2.6.1.1
```
To install Agda, run Stack from the Agda source directory:
```bash
stack install --stack-yaml stack-8.8.3.yaml
```
*This step will take a long time and a lot of memory to complete.*

#### Using an existing installation of GHC
Stack is perfectly capable of installing and managing versions of the [Glasgow Haskell Compiler][haskell-ghc] for you. However, if you already have a copy of GHC installed, and you want Stack to use your system installation, you can pass the `--system-ghc` flag and select the appropriate “stack-*.yaml” file. For instance, if you have GHC 8.2.2 installed, run:
```bash
stack install --system-ghc --stack-yaml stack-8.2.2.yaml
```

#### Check if Agda was installed correctly
If you’d like, you can test to see if you’ve installed Agda correctly. Create a file called “hello.agda” with these lines:
```agda
data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello
```
From a command line, change to the same directory where your “hello.agda” file is located. Then run:
```bash
agda -v 2 hello.agda
```
You should see a short message like the following, but no errors:
```
Checking hello (/path/to/hello.agda).
Finished hello.
```


### Install PLFA and the Agda standard library
You can get the latest version of Programming Language Foundations in Agda from GitHub, either by cloning the repository, or by downloading [the zip archive][plfa-dev]:
```bash
git clone --recurse-submodules https://github.com/plfa/plfa.github.io plfa
```
PLFA ships with the required version of the Agda standard library, so if you cloned with the `--recurse-submodules` flag, you’ve already got, in the “standard-library” directory!

If you forgot to add the `--recurse-submodules` flag, no worries, we can fix that!
```bash
cd plfa/
git submodule update --recursive
```
If you obtained PLFA by downloading the zip archive, you can get the required version of the Agda standard library from GitHub. You can either clone the repository and switch to the correct branch, or you can download the [the zip archive][agda-stdlib]:
```bash
git clone https://github.com/agda/agda-stdlib.git agda-stdlib
cd agda-stdlib
git checkout v1.3
```
Finally, we need to let Agda know where to find the Agda standard library.
You'll need the path where you installed the standard library. Check to see that the file “standard-library.agda-lib” exists, and make a note of the path to this file.
You will need to create two configuration files in “AGDA_DIR”. On UNIX and macOS, “AGDA_DIR” defaults to “~/.agda”. On Windows, “AGDA_DIR” usually defaults to “%AppData%\agda”, where “%AppData%” usually defaults to “C:\Users\USERNAME\AppData\Roaming”.

- If the “AGDA_DIR” directory does not already exist, create it.
- In “AGDA_DIR”, create a plain-text file called “libraries” containing the “/path/to/standard-library.agda-lib”. This lets Agda know that an Agda library called “standard-library” is available.
- In “AGDA_DIR”, create a plain-text file called “defaults” containing *just* the line “standard-library”.

More information about placing the standard libraries is available from [the Library Management page][agda-docs-package-system] of the Agda documentation.

It is possible to set up PLFA as an Agda library as well.  If you want to complete the exercises found in the “courses” folder, or to import modules from the book, you need to do this.  To do so, add the path to “plfa.agda-lib” to “AGDA_DIR/libraries” and add “plfa” to “AGDA_DIR/defaults”, each on a line of their own.

#### Check if the Agda standard library was installed correctly
If you’d like, you can test to see if you’ve installed the Agda standard library correctly. Create a file called “nats.agda” with these lines:
```agda
open import Data.Nat

ten : ℕ
ten = 10
```
(Note that the ℕ is a Unicode character, not a plain capital N. You should be able to just copy-and-paste it from this page into your file.)

From a command line, change to the same directory where your “nats.agda” file is located. Then run:
```bash
agda -v 2 nats.agda
```
You should see a several lines describing the files which Agda loads while checking your file, but no errors:
```
Checking nats (/path/to/nats.agda).
Loading  Agda.Builtin.Equality (…).
…
Loading  Data.Nat (…).
Finished nats.
```


## Setting up an editor for Agda

### Emacs
The recommended editor for Agda is Emacs. To install Emacs:

 - *On UNIX*, the version of Emacs in your repository is probably fine as long as it is fairly recent. There are also links to the most recent release on the [GNU Emacs downloads page][emacs].

 - *On MacOS*, [Aquamacs][aquamacs] is probably the preferred version of Emacs, but GNU Emacs can also be installed via Homebrew or MacPorts. See the [GNU Emacs downloads page][emacs] for instructions.

 - *On Windows*. See the [GNU Emacs downloads page][emacs] for instructions.

Make sure that you are able to open, edit, and save text files with your installation.  The [tour of Emacs][emacs-tour] page on the GNU Emacs site describes how to access the tutorial within your Emacs installation.

Agda ships with the editor support for Emacs built-in, so if you’ve installed Agda, all you have to do to configure Emacs is run:
```bash
agda-mode setup
agda-mode compile
```
If you are already an Emacs user and have customized your setup, you may want to note the configuration which the `setup` appends to your `.emacs` file, and integrate it with your own preferred setup.

#### Check if “agda-mode” was installed correctly
Open the `nats.agda` file you created earlier, and load and type-check the file by typing [`C-c C-l`][agda-docs-emacs-notation].

#### Auto-loading “agda-mode” in Emacs
Since version 2.6.0, Agda has had support for literate editing with Markdown, using the “.lagda.md” extension.  One issue is that Emacs will default to Markdown editing mode for files with a “.md” suffix. In order to have “agda-mode” automatically loaded whenever you open a file ending with “.agda” or “.lagda.md”, add the following line to your Emacs configuration file:
```elisp
;; auto-load agda-mode for .agda and .lagda.md
(setq auto-mode-alist
   (append
     '(("\\.agda\\'" . agda2-mode)
       ("\\.lagda.md\\'" . agda2-mode))
     auto-mode-alist))
```
If you already have settings which change your “auto-mode-alist” in your configuration, put these *after* the ones you already have or combine them if you are comfortable with Emacs Lisp. The configuration file for Emacs is normally located in “HOME/.emacs” or “HOME/.emacs.d/init.el”, but Aquamacs users might need to move their startup settings to the “Preferences.el” file in “HOME/Library/Preferences/Aquamacs Emacs/Preferences”. For Windows, see [the GNU Emacs documentation][emacs-home] for a description of where the Emacs configuration is located.

#### Optional: using the “mononoki” font with Emacs
Agda uses Unicode characters for many key symbols, and it is important that the font which you use to view and edit Agda programs shows these symbols correctly. The most important part is that the font you use has good Unicode support, so while we recommend [mononoki][font-mononoki], fonts such as [Source Code Pro][font-sourcecodepro], [DejaVu Sans Mono][font-dejavusansmono], and [FreeMono][font-freemono] are all good alternatives.

You can download and install mononoki directly from [GitHub][mononoki]. For most systems, installing a font is merely a matter of clicking the downloaded “.otf” or “.ttf” file. If your package manager offers a package for mononoki, that might be easier. For instance, Homebrew on macOS offers the “font-mononoki” package in the [“cask-fonts” cask][cask-fonts], and APT on Debian offers the [“fonts-mononoki” package][font-mononoki-debian]. To configure Emacs to use mononoki as its default font, add the following to the end of your Emacs configuration file:
``` elisp
;; default to mononoki
(set-face-attribute 'default nil
                    :family "mononoki"
                    :height 120
                    :weight 'normal
                    :width  'normal)
```

#### Using “agda-mode” in Emacs
To load and type-check the file, use [`C-c C-l`][agda-docs-emacs-notation].

Agda is edited interactively, using [“holes”][agda-docs-holes], which are bits of the program that are not yet filled in. If you use a question mark as an expression, and load the buffer using “C-c C-l”, Agda replaces the question mark with a hole. There are several things you can to while the cursor is in a hole:

  - `C-c C-c x`: **c**ase split on variable x
  - `C-c C-space`: fill in hole
  - `C-c C-r`: **r**efine with constructor
  - `C-c C-a`: **a**utomatically fill in hole
  - `C-c C-,`: goal type and context
  - `C-c C-.`: goal type, context, and inferred type

See [the emacs-mode docs][agda-docs-emacs-mode] for more details.

If you want to see messages beside rather than below your Agda code, you can do the following:

  - Open your Agda file, and load it using `C-c C-l`;
  - type `C-x 1` to get only your Agda file showing;
  - type `C-x 3` to split the window horizontally;
  - move your cursor to the right-hand half of your frame;
  - type `C-x b` and switch to the buffer called “Agda information”.

Now, error messages from Agda will appear next to your file, rather than squished beneath it.

#### Entering Unicode characters in Emacs with “agda-mode”
When you write Agda code, you will need to insert characters which are not found on standard keyboards. Emacs “agda-mode” makes it easier to do this by defining character translations: when you enter certain sequences of ordinary characters (the kind you find on any keyboard), Emacs will replace them in your Agda file with the corresponding special character.

For example, we can add a comment line to one of the “.agda” test files. Let's say we want to add a comment line that reads:
```
{- I am excited to type ∀ and → and ≤ and ≡ !! -}
```
The first few characters are ordinary, so we would just type them as usual:
```
{- I am excited to type
```
But after that last space, we do not find ∀ on the keyboard. The code for this character is the four characters `\all`, so we type those four characters, and when we finish, Emacs will replace them with what we want:
```
{- I am excited to type ∀
```
We can continue with the codes for the other characters. Sometimes the characters will change as we type them, because a prefix of our character's code is the code of another character. This happens with the arrow, whose code is `\->`.  After typing `\-` we see:
```
{- I am excited to type ∀ and
```
because the code `\-` corresponds to a hyphen of a certain width. When we add the `>`, the `­` becomes `→`! The code for `≤` is `\<=`, and the code for `≡` is `\==`.
```
{- I am excited to type ∀ and → and ≤ and ≡
```
Finally the last few characters are ordinary again,
```
{- I am excited to type ∀ and → and ≤ and ≡ !! -}
```
If you're having trouble typing the Unicode characters into Emacs, the end of each chapter should provide a list of the Unicode characters introduced in that chapter.

Emacs with “agda-mode” offers a number of useful commands, and two of them are especially useful when it comes to working with Unicode characters. For a full list of supported characters, use “agda-input-show-translations” with:

    M-x agda-input-show-translations

All the supported characters in “agda-mode” are shown.

If you want to know how you input a specific Unicode character in agda file, move the cursor onto the character and type the following command:

    M-x quail-show-key

You'll see the key sequence of the character in mini buffer.

### Spacemacs
[Spacemacs][spacemacs] is a “community-driven Emacs distribution” with native support for both Emacs and Vim editing styles. It comes with [integration for “agda-mode”][spacemacs-agda] out of the box. All that is required is that you turn it on.

### Visual Studio Code
[Visual Studio Code][vscode] is a free source code editor developed by Microsoft. There is [a plugin for Agda support][vscode-agda] available on the Visual Studio Marketplace.

### Atom
[Atom][atom] is a free source code editor developed by GitHub. There is [a plugin for Agda support][atom-agda] available on the Atom package manager.

## Dependencies for developers
PLFA is written in literate Agda with [Pandoc Markdown][pandoc-markdown].
PLFA is available as both a website and an EPUB e-book, both of which can be built on UNIX and macOS.
Finally, to help developers avoid common mistakes, we provide a set of Git hooks.


### Building the website and e-book
If you’d like to build the web version of PLFA locally, [Stack](#install-the-haskell-tool-stack) is all you need! PLFA is built using [Hakyll][hakyll], a Haskell library for building static websites. We’ve setup a Makefile to help you run common tasks. For instance, to build PLFA, run:
```bash
make build
```
If you’d like to serve PLFA locally, rebuilding the website when any of the source files are changed, run:
```bash
make watch
```
The Makefile offers more than just building and watching, it also offers the following useful options:
```
build                      # Build PLFA
watch                      # Build and serve PLFA, monitor for changes and rebuild
test                       # Test web version for broken links, invalid HTML, etc.
test-epub                  # Test EPUB for compliance to the EPUB3 standard
clean                      # Clean PLFA build
init                       # Setup the Git hooks (see below)
update-contributors        # Pull in new contributors from GitHub to contributors/
list                       # List all build targets
```
For completeness, the Makefile also offers the following options, but you’re unlikely to need these:
```
legacy-versions            # Build legacy versions of PLFA
setup-install-bundler      # Install Ruby Bundler (needed for ‘legacy-versions’)
setup-install-htmlproofer  # Install HTMLProofer (needed for ‘test’ and Git hooks)
setup-check-fix-whitespace # Check to see if fix-whitespace is installed (needed for Git hooks)
setup-check-epubcheck      # Check to see if epubcheck is installed (needed for EPUB tests)
setup-check-gem            # Check to see if RubyGems is installed
setup-check-npm            # Check to see if the Node Package Manager is installed
setup-check-stack          # Check to see if the Haskell Tool Stack is installed
```
The [EPUB version][epub] of the book is built as part of the website, since it’s hosted on the website.


### Git hooks
The repository comes with several Git hooks:

 1. The [fix-whitespace][fix-whitespace] program is run to check for whitespace violations.

 2. The test suite is run to check if everything type checks.

You can install these Git hooks by calling “make init”.
You can install [fix-whitespace][fix-whitespace] by running:
```bash
git clone https://github.com/agda/fix-whitespace
cd fix-whitespace/
stack install --stack-yaml stack-8.8.3.yaml
```
If you want Stack to use your system installation of GHC, follow the instructions for [Using an existing installation of GHC](#using-an-existing-installation-of-ghc).

<!-- Links -->

[epub]: https://plfa.github.io/plfa.epub
[plfa]: http://plfa.inf.ed.ac.uk
[plfa-dev]: https://github.com/plfa/plfa.github.io/archive/dev.zip
[plfa-status]: https://travis-ci.org/plfa/plfa.github.io.svg?branch=dev
[plfa-travis]: https://travis-ci.org/plfa/plfa.github.io
[plfa-calver]: https://img.shields.io/badge/calver-20.07-22bfda
[plfa-latest]: https://github.com/plfa/plfa.github.io/releases/latest
[plfa-master]: https://github.com/plfa/plfa.github.io/archive/master.zip
[haskell-stack]:  https://docs.haskellstack.org/en/stable/README/
[haskell-ghc]: https://www.haskell.org/ghc/
[git]: https://git-scm.com/downloads
[agda]: https://github.com/agda/agda/releases/tag/v2.6.1.1
[agda-version]: https://img.shields.io/badge/agda-v2.6.1.1-blue.svg
[agda-docs-holes]: https://agda.readthedocs.io/en/v2.6.1.1/getting-started/quick-guide.html
[agda-docs-emacs-mode]: https://agda.readthedocs.io/en/v2.6.1.1/tools/emacs-mode.html
[agda-docs-emacs-notation]: https://agda.readthedocs.io/en/v2.6.1.1/tools/emacs-mode.html#notation-for-key-combinations
[agda-docs-package-system]: https://agda.readthedocs.io/en/v2.6.1.1/tools/package-system.html#example-using-the-standard-library
[emacs]: https://www.gnu.org/software/emacs/download.html
[emacs-tour]: https://www.gnu.org/software/emacs/tour/
[emacs-home]: https://www.gnu.org/software/emacs/manual/html_node/efaq-w32/Location-of-init-file.html
[aquamacs]: http://aquamacs.org/
[spacemacs]: https://www.spacemacs.org/
[spacemacs-agda]: https://develop.spacemacs.org/layers/+lang/agda/README.html
[vscode]: https://code.visualstudio.com/
[vscode-agda]: https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode
[atom]: https://atom.io/
[atom-agda]: https://atom.io/packages/agda-mode
[agda-stdlib-version]: https://img.shields.io/badge/agda--stdlib-v1.3-blue.svg
[agda-stdlib]: https://github.com/agda/agda-stdlib/releases/tag/v1.3
[fix-whitespace]: https://github.com/agda/fix-whitespace
[ruby]: https://www.ruby-lang.org/en/documentation/installation/
[ruby-bundler]: https://bundler.io/#getting-started
[ruby-jekyll]: https://jekyllrb.com/
[ruby-html-proofer]: https://github.com/gjtorikian/html-proofer
[hakyll]: https://jaspervdj.be/hakyll/
[pandoc]: https://pandoc.org/installing.html
[pandoc-markdown]: https://pandoc.org/MANUAL.html#pandocs-markdown
[commonmark]: https://commonmark.org/
[epubcheck]: https://github.com/w3c/epubcheck
[xcode]: https://developer.apple.com/xcode/
[font-sourcecodepro]: https://github.com/adobe-fonts/source-code-pro
[font-dejavusansmono]: https://dejavu-fonts.github.io/
[font-freemono]: https://www.gnu.org/software/freefont/
[font-mononoki]: https://madmalik.github.io/mononoki/
[font-mononoki-debian]: https://packages.debian.org/sid/fonts/fonts-mononoki
[cask-fonts]: https://github.com/Homebrew/homebrew-cask-fonts
