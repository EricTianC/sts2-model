using System;

namespace MegaCrit.Sts2.Core.Modding
{
    [AttributeUsage(AttributeTargets.Class, Inherited = false)]
    public class ModInitializerAttribute : Attribute
    {
        public string initializerMethod;

        public ModInitializerAttribute(string initializerMethod)
        {
            this.initializerMethod = initializerMethod;
        }
    }
}

namespace MegaCrit.Sts2.Core.Logging
{
    public static class Log
    {
        public static void Info(string text, int skipFrames = 2) => Console.WriteLine($"[INFO] {text}");
        public static void Warn(string text, int skipFrames = 2) => Console.WriteLine($"[WARN] {text}");
        public static void Error(string text, int skipFrames = 2) => Console.Error.WriteLine($"[ERROR] {text}");
        public static void Debug(string text, int skipFrames = 2) => Console.WriteLine($"[DEBUG] {text}");
    }
}
