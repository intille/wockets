using System;
using System.Reflection;

namespace Wockets.Utils.Tapi
{
    /// <summary>
    /// Summary description for ByteCopy.
    /// </summary>
    public class ByteCopy
    {
        public ByteCopy()
        {
            //
            // TODO: Add constructor logic here
            //
        }

        static public void ByteArrayToStruct(byte[] data, object target)
        {
            int index = 0;
            ByteArrayToStruct(data, ref index, target);
        }

        static private void ByteArrayToStruct(byte[] data, ref int index, object target)
        {
            int i = index;
            foreach (FieldInfo fi in target.GetType().GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
            {
                Type t = fi.FieldType;
                if (t.GetCustomAttributes(typeof(InternalAttribute), false).Length > 0)
                    continue;

                if (t.IsArray)
                {
                    if (t.GetElementType() != typeof(byte))
                        throw new NotSupportedException(string.Format("Field {0}: Only byte arrays are supported", fi.Name));
                    object[] colAttr = fi.GetCustomAttributes(typeof(ArrayAttribute), true);
                    if (colAttr.Length != 1)
                        throw new NotSupportedException(string.Format("Field {0}: Must have Array attribute with size specified", fi.Name));
                    int size = (colAttr[0] as ArrayAttribute).Size;
                    byte[] fieldData = new byte[size];
                    Array.Copy(data, i, fieldData, 0, size);
                    fi.SetValue(target, fieldData);
                    i += size;
                    continue;
                }

                if (t == typeof(byte) || t == typeof(sbyte))
                    fi.SetValue(target, data[i++]);
                else if (t == typeof(short))
                {
                    fi.SetValue(target, BitConverter.ToInt16(data, i));
                    i += 2;
                }
                else if (t == typeof(ushort))
                {
                    fi.SetValue(target, BitConverter.ToUInt16(data, i));
                    i += 2;
                }
                else if (t == typeof(Int32))
                {
                    fi.SetValue(target, BitConverter.ToInt32(data, i));
                    i += 4;
                }
                else if (t == typeof(UInt32))
                {
                    fi.SetValue(target, BitConverter.ToUInt32(data, i));
                    i += 4;
                }
                else if (t == typeof(IntPtr))
                {
                    fi.SetValue(target, (IntPtr)BitConverter.ToInt32(data, i));
                    i += 4;
                }
                else if (t == typeof(UIntPtr))
                {
                    fi.SetValue(target, (UIntPtr)BitConverter.ToUInt32(data, i));
                    i += 4;
                }
                else if (t.IsValueType && t.GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance).Length > 0)
                {
                    object o = Activator.CreateInstance(t);
                    ByteArrayToStruct(data, ref i, o);
                    fi.SetValue(target, o);
                }
            }
            index = i;
        }

        static public void StructToByteArray(object source, byte[] data)
        {
            int index = 0;
            StructToByteArray(source, ref index, data);
        }

        static public void StructToByteArray(object source, ref int index, byte[] data)
        {
            int i = index;
            foreach (FieldInfo fi in source.GetType().GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance))
            {
                Type t = fi.FieldType;
                if (t.GetCustomAttributes(typeof(InternalAttribute), false).Length > 0)
                    continue;

                if (t.IsArray)
                {
                    if (t.GetElementType() != typeof(byte))
                        throw new NotSupportedException(string.Format("Field {0}: Only byte arrays are supported", fi.Name));
                    object[] colAttr = fi.GetCustomAttributes(typeof(ArrayAttribute), true);
                    if (colAttr.Length != 1)
                        throw new NotSupportedException(string.Format("Field {0}: Must have Array attribute with size specified", fi.Name));
                    int size = (colAttr[0] as ArrayAttribute).Size;
                    byte[] fieldData = (byte[])fi.GetValue(source);
                    Array.Copy(fieldData, 0, data, i, System.Math.Min(size, fieldData.Length));
                    i += System.Math.Min(size, fieldData.Length);
                    continue;
                }

                if (t == typeof(byte))
                    data[i++] = (byte)fi.GetValue(source);
                else if (t == typeof(sbyte))
                    data[i++] = (byte)fi.GetValue(source);
                else if (t == typeof(short))
                {
                    BitConverter.GetBytes((short)fi.GetValue(source)).CopyTo(data, i);
                    i += 2;
                }
                else if (t == typeof(ushort))
                {
                    BitConverter.GetBytes((ushort)fi.GetValue(source)).CopyTo(data, i);
                    i += 2;
                }
                else if (t == typeof(Int32))
                {
                    BitConverter.GetBytes((Int32)fi.GetValue(source)).CopyTo(data, i);
                    i += 4;
                }
                else if (t == typeof(UInt32))
                {
                    BitConverter.GetBytes((uint)fi.GetValue(source)).CopyTo(data, i);
                    i += 4;
                }
                else if (t == typeof(IntPtr))
                {
                    BitConverter.GetBytes(((IntPtr)fi.GetValue(source)).ToInt32()).CopyTo(data, i);
                    i += 4;
                }
                else if (t == typeof(UIntPtr))
                {
                    BitConverter.GetBytes(((UIntPtr)fi.GetValue(source)).ToUInt32()).CopyTo(data, i);
                    i += 4;
                }
                else if (t.IsValueType && t.GetFields(BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance).Length > 0)
                {
                    object o = fi.GetValue(source);
                    StructToByteArray(o, ref i, data);
                }
            }
            index = i;
        }
    }

    [AttributeUsage(AttributeTargets.Field)]
    class InternalAttribute : Attribute
    {
    }

    [AttributeUsage(AttributeTargets.Field)]
    class ArrayAttribute : Attribute
    {
        public int Size;
        public ArrayAttribute(int size)
        {
            Size = size;
        }
    }

}
