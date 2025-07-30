# 🔐 NSPK Protocol Visualisation & Formal Model

An interactive visualisation and formal verification tool for the Needham-Schroeder Public-Key (NSPK) protocol.  
This project combines **formal methods**, **cryptographic protocol modelling**, and an **SVG-based front-end** to simulate and explore secure communications—along with known attacks.

---

## 📘 Overview

This tool models the **NSPK security protocol** using the **B-Method** and visualises it through a custom **event-driven UI**. It allows users to:

- Observe step-by-step execution of the protocol
- Trigger events (e.g., send/receive messages)
- Visualise protocol state and message exchange
- Simulate known vulnerabilities like **Lowe's attack**
- Explore adversary behaviour through a **Spy model** with deductive logic

Designed as part of a formal software engineering project, this tool aims to **bridge the gap between formal verification and real-world system understanding**, supporting both technical analysis and educational use.

---

## 🧰 Technologies Used

| Area | Tools / Languages |
|------|-------------------|
| **Formal Methods** | [B-Method](https://en.wikipedia.org/wiki/B-Method), [ProB2-UI](https://www3.hhu.de/stups/prob/index.php/ProB_2_UI) |
| **UI/Visualisation** | SVG, HTML, CSS |
| **Logic Integration** | JSON-based conditional rendering |
| **Model Behaviour** | Set theory, function mappings, precondition enforcement |
| **Development Methodology** | Agile (8 iterations), test-driven refinement |

---

## 🚀 Features

- ✅ Full model of NSPK with formal send/receive operations  
- ✅ Spy simulation with message deduction and construction  
- ✅ Role-based protocol logic with belief systems  
- ✅ Event-driven visualisation linked to model state  
- ✅ Static and interactive UI modes  
- ✅ Support for detecting **protocol misuse** and **security violations**

---

---

## 🖥️ How to Use

### ✅ Requirements

- [ProB2-UI](https://www3.hhu.de/stups/prob/index.php/ProB_2_UI) (install instructions on their site)
- Modern web browser (Chrome, Firefox, etc.)

### 📦 Running the Model

1. Open ProB2-UI
2. Load the main model file:  
   `model/nspk_machine.mch`
3. Use the **Operation view** to trigger steps of the protocol (e.g., send/receive messages, spy deduction)

### 🌐 Running the UI

1. Open `index.html` in prob2-ui
2. Trigger events via the model (or UI buttons if enabled)
3. Visual elements (e.g., messages, keys) will appear or change based on the current protocol state, controlled via `display.json`

---

## 🔍 Example Scenarios

- **Normal run**: Visualise a secure 3-step exchange between Alice and Bob  
- **Attack simulation**: Observe how a spy can intercept and reuse a message to impersonate a participant  
- **Belief failure**: See what happens when role assumptions break due to lack of authentication  

---

## 📚 Learning Goals

- Explore how formal modelling supports protocol security
- Learn the importance of nonces, key exchange, and authentication
- Visualise how **deductive adversaries** can break assumptions in cryptographic design

---

## 🤝 Contributions & Extensions

This project was developed as part of a formal software engineering thesis with a focus on:

- Secure software design
- Formal verification
- Human-centric visualisation of cryptographic behaviour

Future work could include:
- TLS/SSL protocol variants
- Additional attack patterns (replay, man-in-the-middle)
- UI enhancements with animation and mobile support

---

## 👤 Author

**Nicolas Romero**  
Cyber Security Graduate

**Supervisor**
Dr. David Williams.

---

> “Build systems that people trust by helping them understand how they work.”


