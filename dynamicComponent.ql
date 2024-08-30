/**
 * Comprehensive query to find dynamically registered components in OEM apps
 * with minimal false negatives
 */

import java
import android
import semmle.code.java.dataflow.DataFlow

// Helper predicate for general registration methods
predicate isRegistrationMethod(Method m) {
  m.getName().matches("register%") or
  m.getName().matches("add%") or
  m.getName().matches("set%") or
  m.getName().matches("create%") or
  m.getName().matches("start%") or
  m.getName().matches("bind%") or
  m.getName().matches("attach%")
}

// Find all potential dynamic registrations
from MethodAccess ma, Method m
where 
  ma.getMethod() = m and
  (
    // Known Android framework registration methods
    (m.getDeclaringType().getPackage().getName().matches("android%") and isRegistrationMethod(m))
    or
    // ServiceManager methods
    (m.getDeclaringType().hasQualifiedName("android.os", "ServiceManager") and m.getName().matches("add%"))
    or
    // Settings Provider methods
    (m.getDeclaringType().hasQualifiedName("android.provider", "Settings$System") and m.getName().matches("put%"))
    or
    // ContentResolver methods
    (m.getDeclaringType().hasQualifiedName("android.content", "ContentResolver") and m.getName().matches("register%"))
    or
    // WindowManager methods
    (m.getDeclaringType().hasQualifiedName("android.view", "WindowManager") and m.getName().matches("add%"))
    or
    // PackageManager methods for component enabling
    (m.getDeclaringType().hasQualifiedName("android.content.pm", "PackageManager") and m.getName() = "setComponentEnabledSetting")
    or
    // Activity methods that might involve dynamic registration
    (m.getDeclaringType().hasQualifiedName("android.app", "Activity") and 
     (m.getName() = "startActivity" or m.getName() = "startActivityForResult"))
    or
    // Fragment transactions
    (m.getDeclaringType().hasQualifiedName("androidx.fragment.app", "FragmentTransaction") and 
     (m.getName() = "add" or m.getName() = "replace"))
    or
    // Any method call with 'register', 'add', or 'set' in its name (catch-all)
    isRegistrationMethod(m)
  )
select ma, "Potential dynamic registration found: " + m.getName()

// Find classes that extend known Android components
from Class c
where 
  c.getASupertype*().hasQualifiedName("android.content", "ContentProvider") or
  c.getASupertype*().hasQualifiedName("android.app", "Service") or
  c.getASupertype*().hasQualifiedName("android.content", "BroadcastReceiver") or
  c.getASupertype*().hasQualifiedName("android.app", "Activity") or
  c.getASupertype*().hasQualifiedName("androidx.fragment.app", "Fragment")
select c, "Potential dynamically registerable component: " + c.getName()

// Find reflection usage that might indicate dynamic registration
from MethodAccess ma
where 
  ma.getMethod().getDeclaringType().hasQualifiedName("java.lang.reflect", "Method") and
  ma.getMethod().hasName("invoke")
select ma, "Reflection used, potential dynamic registration"

// Find dynamic proxy creation
from MethodAccess ma
where 
  ma.getMethod().getDeclaringType().hasQualifiedName("java.lang.reflect", "Proxy") and
  ma.getMethod().hasName("newProxyInstance")
select ma, "Dynamic proxy created, potential dynamic registration"

// Find usage of ClassLoader methods that might load components dynamically
from MethodAccess ma
where 
  ma.getMethod().getDeclaringType().getASupertype*().hasQualifiedName("java.lang", "ClassLoader") and
  (ma.getMethod().hasName("loadClass") or ma.getMethod().hasName("defineClass"))
select ma, "ClassLoader method used, potential dynamic component loading"

// Find dynamic receiver registration in manifests
from XmlElement element
where 
  element.getName() = "receiver" and
  element.getAttributeValue("android:enabled") = "false"
select element, "Receiver in manifest with android:enabled='false', potential dynamic enablement"

// Find dynamic content provider registration in manifests
from XmlElement element
where 
  element.getName() = "provider" and
  element.getAttributeValue("android:enabled") = "false"
select element, "Provider in manifest with android:enabled='false', potential dynamic enablement"

// Find dynamic service registration in manifests
from XmlElement element
where 
  element.getName() = "service" and
  element.getAttributeValue("android:enabled") = "false"
select element, "Service in manifest with android:enabled='false', potential dynamic enablement"

// Find potential custom registration methods in OEM-specific classes
from Method m
where 
  isRegistrationMethod(m) and
  not m.getDeclaringType().getPackage().getName().matches("android%") and
  not m.getDeclaringType().getPackage().getName().matches("java%") and
  not m.getDeclaringType().getPackage().getName().matches("javax%")
select m, "Potential custom registration method in OEM class: " + m.getQualifiedName()