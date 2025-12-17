package main

import (
	"crypto/rand"
	"encoding/base64"
	"encoding/hex"
	"errors"
	"fmt"
	"math"
	"strings"

	"fyne.io/fyne/v2"
	"fyne.io/fyne/v2/app"
	"fyne.io/fyne/v2/container"
	"fyne.io/fyne/v2/dialog"
	"fyne.io/fyne/v2/layout"
	"fyne.io/fyne/v2/widget"
)

type RC5 struct {
	W int
	R int
	B int
	C int
	S []uint32
}

const (
	W   = 32
	R   = 12
	P32 = 0xB7E15163
	Q32 = 0x9E3779B9
)

func NewRC5() *RC5 {
	return &RC5{
		W: W,
		R: R,
	}
}

func (rc5 *RC5) rol(value uint32, shift int) uint32 {
	shift %= 32
	return (value << shift) | (value >> (32 - shift))
}

func (rc5 *RC5) ror(value uint32, shift int) uint32 {
	shift %= 32
	return (value >> shift) | (value << (32 - shift))
}

func (rc5 *RC5) keyExpansion(key []byte) {
	rc5.S = make([]uint32, 2*(rc5.R+1))

	L := make([]uint32, rc5.C)

	for i := 0; i < rc5.B; i++ {
		idx := i / 4
		L[idx] = (L[idx] << 8) | uint32(key[i])
	}

	rc5.S[0] = P32
	for i := 1; i < 2*(rc5.R+1); i++ {
		rc5.S[i] = rc5.S[i-1] + Q32
	}

	var A, B_local uint32
	i1, j := 0, 0
	v := 3 * max(2*(rc5.R+1), rc5.C)

	for counter := 0; counter < v; counter++ {
		A = rc5.S[i1] + A + B_local
		rc5.S[i1] = rc5.rol(A, 3)
		A = rc5.S[i1]

		B_local = L[j] + A + B_local
		L[j] = rc5.rol(B_local, int(A+B_local))
		B_local = L[j]

		i1 = (i1 + 1) % (2 * (rc5.R + 1))
		j = (j + 1) % rc5.C
	}
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func (rc5 *RC5) convertToBlocks(data []byte) []uint32 {
	blockCount := ((len(data) + 7) / 8) * 2
	blocks := make([]uint32, blockCount)

	for i := 0; i < len(data); i += 4 {
		var block uint32
		for j := 0; j < 4 && i+j < len(data); j++ {
			block |= uint32(data[i+j]) << (j * 8)
		}
		blocks[i/4] = block
	}

	return blocks
}

func (rc5 *RC5) convertToBytes(blocks []uint32) []byte {
	result := make([]byte, len(blocks)*4)

	for i := 0; i < len(blocks); i++ {
		block := blocks[i]
		for j := 0; j < 4; j++ {
			result[i*4+j] = byte(block >> (j * 8))
		}
	}

	return result
}

func (rc5 *RC5) Encode(text, key string) (string, error) {
	keyBytes, err := base64.StdEncoding.DecodeString(key)
	if err != nil {
		return "", fmt.Errorf("неверный формат ключа (должен быть Base64): %v", err)
	}

	rc5.B = len(keyBytes)
	rc5.C = rc5.B / 4
	if rc5.B%4 != 0 {
		rc5.C++
	}

	rc5.keyExpansion(keyBytes)

	textBytes := []byte(text)
	blocks := rc5.convertToBlocks(textBytes)

	if len(blocks)%2 != 0 {
		blocks = append(blocks, 0)
	}

	for i := 0; i < len(blocks); i += 2 {
		A := blocks[i]
		B := blocks[i+1]

		A = A + rc5.S[0]
		B = B + rc5.S[1]

		for j := 1; j <= rc5.R; j++ {
			A = rc5.rol(A^B, int(B)) + rc5.S[2*j]
			B = rc5.rol(B^A, int(A)) + rc5.S[2*j+1]
		}

		blocks[i] = A
		blocks[i+1] = B
	}

	resultBytes := rc5.convertToBytes(blocks)
	return base64.StdEncoding.EncodeToString(resultBytes), nil
}

func (rc5 *RC5) Decode(cipherText, key string) (string, error) {
	keyBytes, err := base64.StdEncoding.DecodeString(key)
	if err != nil {
		return "", fmt.Errorf("неверный формат ключа (должен быть Base64) %v", err)
	}

	cipherBytes, err := base64.StdEncoding.DecodeString(cipherText)
	if err != nil {
		return "", fmt.Errorf("неверный формат шифртекста (должен быть Base64) %v", err)
	}

	rc5.B = len(keyBytes)
	rc5.C = rc5.B / 4
	if rc5.B%4 != 0 {
		rc5.C++
	}

	rc5.keyExpansion(keyBytes)

	blocks := rc5.convertToBlocks(cipherBytes)

	if len(blocks)%2 != 0 {
		return "", errors.New("неверная длина шифртекста")
	}

	for i := 0; i < len(blocks); i += 2 {
		A := blocks[i]
		B := blocks[i+1]

		for j := rc5.R; j >= 1; j-- {
			B = rc5.ror(B-rc5.S[2*j+1], int(A)) ^ A
			A = rc5.ror(A-rc5.S[2*j], int(B)) ^ B
		}

		B = B - rc5.S[1]
		A = A - rc5.S[0]

		blocks[i] = A
		blocks[i+1] = B
	}

	resultBytes := rc5.convertToBytes(blocks)
	resultBytes = []byte(strings.TrimRight(string(resultBytes), "\x00"))

	return string(resultBytes), nil
}

func (rc5 *RC5) Hash(message string) string {
	key := "dsfsdfsdkfsdfgskfgsglsgfs"
	keyBytes := []byte(key)

	if len(keyBytes) < rc5.B {
		padding := make([]byte, rc5.B-len(keyBytes))
		keyBytes = append(keyBytes, padding...)
	} else if len(keyBytes) > rc5.B {
		keyBytes = keyBytes[:rc5.B]
	}

	rc5.B = len(keyBytes)
	rc5.C = rc5.B / 4
	if rc5.B%4 != 0 {
		rc5.C++
	}

	rc5.keyExpansion(keyBytes)

	H_prev := make([]byte, 24)

	messageBytes := []byte(message)
	blockCount := (len(messageBytes) + 23) / 24

	for i := 0; i < blockCount; i++ {
		M_i := make([]byte, 24)
		bytesToCopy := int(math.Min(24, float64(len(messageBytes)-i*24)))
		copy(M_i, messageBytes[i*24:i*24+bytesToCopy])

		for j := 0; j < 24; j++ {
			H_prev[j] ^= M_i[j]
		}

		encryptedHPrev, err := rc5.Encode(base64.StdEncoding.EncodeToString(H_prev),
			base64.StdEncoding.EncodeToString(M_i))
		if err != nil {
			return hex.EncodeToString(H_prev)
		}

		E_H_prev, err := base64.StdEncoding.DecodeString(encryptedHPrev)
		if err != nil {
			return hex.EncodeToString(H_prev)
		}

		H_i := make([]byte, 24)
		for j := 0; j < 24; j++ {
			H_i[j] = E_H_prev[j] ^ M_i[j] ^ H_prev[j]
		}

		H_prev = H_i
	}

	hashBase64 := base64.StdEncoding.EncodeToString(H_prev)
	if len(hashBase64) > 32 {
		return hashBase64[:32]
	}
	return hashBase64
}

func (rc5 *RC5) genRandomKey() string {
	keyLength := 16
	keyBytes := make([]byte, keyLength)
	_, err := rand.Read(keyBytes)
	if err != nil {
		return base64.StdEncoding.EncodeToString([]byte("ddfdfsdfdsf"))
	}
	return base64.StdEncoding.EncodeToString(keyBytes)
}

func main() {
	a := app.New()
	w := a.NewWindow("")
	w.Resize(fyne.NewSize(600, 600))
	rc5 := NewRC5()

	tabs := container.NewAppTabs(
		container.NewTabItem("Шифрование", makeEncryptionTab(w, rc5)),
		container.NewTabItem("Хеширование", makeHashingTab(w, rc5)),
	)

	w.SetContent(tabs)
	w.ShowAndRun()
}

func makeEncryptionTab(w fyne.Window, rc5 *RC5) fyne.CanvasObject {
	input := widget.NewMultiLineEntry()
	input.SetPlaceHolder("Введите текст")
	input.SetMinRowsVisible(5)

	lKey := widget.NewLabel("Ключ (Base64)")
	keyE := widget.NewEntry()
	keyE.SetPlaceHolder("Введите ключ в формате Base64")
	keyE.Validator = func(s string) error {
		if s == "" {
			return errors.New("ключ не может быть пустым")
		}
		_, err := base64.StdEncoding.DecodeString(s)
		if err != nil {
			return errors.New("неверный формат Base64")
		}
		return nil
	}

	btnGenKey := widget.NewButton("Случайный ключ", func() {
		keyE.SetText(rc5.genRandomKey())
	})

	output := widget.NewMultiLineEntry()
	output.SetPlaceHolder("Результат")
	output.Disable()
	output.SetMinRowsVisible(5)

	btnEnc := widget.NewButton("Зашифровать", func() {
		text := input.Text
		key := keyE.Text

		if text == "" || key == "" {
			dialog.ShowInformation("Внимание", "Введите текст и ключ", w)
			return
		}

		res, err := rc5.Encode(text, key)
		if err != nil {
			dialog.ShowError(err, w)
			return
		}
		output.SetText(res)
	})

	btnDec := widget.NewButton("Расшифровать", func() {
		text := input.Text
		key := keyE.Text

		if text == "" || key == "" {
			dialog.ShowInformation("Внимание", "Введите шифртекст (Base64) и ключ", w)
			return
		}

		res, err := rc5.Decode(text, key)
		if err != nil {
			dialog.ShowError(err, w)
			return
		}
		output.SetText(res)
	})

	btnClear := widget.NewButton("Очистить", func() {
		input.SetText("")
		output.SetText("")
	})

	buttons := container.New(layout.NewGridLayout(3), btnEnc, btnDec, btnClear)
	keyCont := container.NewBorder(nil, nil, nil, btnGenKey, keyE)

	content := container.NewVBox(
		widget.NewLabel("Текст"),
		input,
		lKey,
		keyCont,
		buttons,
		widget.NewLabel("Результат"),
		output,
	)

	return container.NewScroll(content)
}

func makeHashingTab(w fyne.Window, rc5 *RC5) fyne.CanvasObject {
	input := widget.NewMultiLineEntry()
	input.SetPlaceHolder("Введите текст")
	input.SetMinRowsVisible(5)

	output := widget.NewMultiLineEntry()
	output.SetPlaceHolder("Хеш")
	output.Disable()
	output.SetMinRowsVisible(5)

	formatSelector := widget.NewSelect([]string{"Base64", "Hex", "Base64 (32 символа)"}, func(s string) {})
	formatSelector.SetSelected("Base64 (32 символа)")

	btnHash := widget.NewButton("Вычислить хеш", func() {
		text := input.Text
		if text == "" {
			dialog.ShowInformation("Внимание", "Введите текст для хеширования", w)
			return
		}

		hash := rc5.Hash(text)

		format := formatSelector.Selected
		switch format {
		case "Hex":
			hashBytes, err := base64.StdEncoding.DecodeString(hash)
			if err == nil {
				output.SetText(hex.EncodeToString(hashBytes))
			} else {
				output.SetText(hash)
			}
		case "Base64":
			output.SetText(hash)
		case "Base64 (32 символа)":
			if len(hash) > 32 {
				output.SetText(hash[:32])
			} else {
				output.SetText(hash)
			}
		}
	})

	btnClear := widget.NewButton("Очистить", func() {
		input.SetText("")
		output.SetText("")
	})

	buttons := container.New(layout.NewGridLayout(2), btnHash, btnClear)

	content := container.NewVBox(
		widget.NewLabel("Текст для хеширования"),
		input,
		widget.NewLabel("Формат вывода"),
		formatSelector,
		buttons,
		widget.NewLabel("Хеш"),
		output,
	)

	return container.NewScroll(content)
}
