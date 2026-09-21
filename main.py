import tkinter as tk

root = tk.Tk()
root.title("Viju Test App")
root.geometry("400x200")

label = tk.Label(
    root,
    text="Windows EXE working!",
    font=("Arial", 18)
)
label.pack(pady=60)

root.mainloop()