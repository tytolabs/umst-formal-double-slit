import re

with open("README.md", "r") as f:
    text = f.read()

pw_match = re.search(r'(### Knowing in plain words\n\n.*?\n### Visual surrogate \(static teaser\)\n\n.*?)\n## 1\.', text, flags=re.DOTALL)
if not pw_match:
    pw_match = re.search(r'(### Knowing in plain words\n\n.*?)\n## 1\.', text, flags=re.DOTALL)

if not pw_match:
    print("Could not find Knowing in plain words")
    exit(1)

pw_text = pw_match.group(1)
# Remove pw_text from text
text = text.replace(pw_text, "")

honest_match = re.search(r'(\*\*Honest is / isn\'t\.\*\*.*?\n)\n', text, flags=re.DOTALL)
honest_text = ""
if honest_match:
    honest_text = honest_match.group(1)
    text = text.replace(honest_text + "\n", "")

hot_match = re.search(r'(### Hot arena vs cold edge \(performance honesty\)\n\n.*?)\n### Honesty ledger', text, flags=re.DOTALL)
hot_text = ""
if hot_match:
    hot_text = hot_match.group(1)
    text = text.replace(hot_text, "")

ledger_match = re.search(r'(### Honesty ledger \(one status pointer\)\n\n.*?)\n## 10\.', text, flags=re.DOTALL)
ledger_text = ""
if ledger_match:
    ledger_text = ledger_match.group(1)
    text = text.replace(ledger_text, "")
else:
    # try until <details>
    ledger_match = re.search(r'(### Honesty ledger \(one status pointer\)\n\n.*?)\n<details>', text, flags=re.DOTALL)
    if ledger_match:
        ledger_text = ledger_match.group(1)
        text = text.replace(ledger_text, "")

what_it_is_idx = text.find("**What it is.**")
if what_it_is_idx != -1:
    text = text[:what_it_is_idx] + pw_text + "\n\n" + text[what_it_is_idx:]
else:
    print("Could not find What it is.")

text = text.replace("## 10. Conclusion:", "## 11. Conclusion:")

limits_section = f"\n## 10. Honesty and limits\n\n{honest_text}\n{hot_text}{ledger_text}"
conclusion_idx = text.find("## 11. Conclusion:")
if conclusion_idx != -1:
    text = text[:conclusion_idx] + limits_section + text[conclusion_idx:]

text = text.replace("- [§10 Conclusion](#10-conclusion-inferences--forward-path)", "- [§10 Honesty and limits](#10-honesty-and-limits)\n- [§11 Conclusion](#11-conclusion-inferences--forward-path)")
text = text.replace(" | [§10](#10-conclusion-inferences--forward-path) |", " | [§10](#10-honesty-and-limits) · [§11](#11-conclusion-inferences--forward-path) |")

with open("README.md", "w") as f:
    f.write(text)

